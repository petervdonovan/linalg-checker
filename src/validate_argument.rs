use std::{
    collections::BTreeSet,
    error::Error,
    fmt::{self, Display},
    rc::Rc,
};

use markdown::mdast::{Heading, Html, InlineMath, List, ListItem, Node, Paragraph, Root};
use z3::{SatResult, Solver, ast::Bool};

pub use crate::model_finding::{ModelFindingError, ToFromMd};
use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Model, NaturalParameter, RawExpr, TypeExpr,
    enumerable_envspec::{
        ShapeError, extract_prepared_environment_iterator, infer_symbolic_type_environment,
    },
    model_finding::{
        assert_definitions, assert_natural_assignment, expression_list, extract_model, heading,
        heading_text, lower_prepared_boolean, parse_expression_item, parse_expression_section,
        render_md, root, root_children, section_start, z3_boolean,
    },
    preprocessing::{PreparedExpression, prepare_expression},
    to_z3::{LoweredExistence, LoweredSideCondition},
    type_resolver::SymbolicTypeEnvironment,
    visit_mut::VisitContext,
};

const POSITIVE: VisitContext = VisitContext {
    logical_polarity: true,
};
const NEGATIVE: VisitContext = VisitContext {
    logical_polarity: false,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgumentValidationError {
    Shape(ShapeError),
    ModelFinding(ModelFindingError),
}

impl Display for ArgumentValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape(error) => error.fmt(f),
            Self::ModelFinding(error) => error.fmt(f),
        }
    }
}

impl Error for ArgumentValidationError {}

impl From<ShapeError> for ArgumentValidationError {
    fn from(error: ShapeError) -> Self {
        Self::Shape(error)
    }
}

impl From<ModelFindingError> for ArgumentValidationError {
    fn from(error: ModelFindingError) -> Self {
        Self::ModelFinding(error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepCheck {
    Unsat {
        environment: Rc<Environment>,
        supporting_facts: Vec<Expr<()>>,
    },
    Counterexample {
        environment: Rc<Environment>,
        model: Model,
    },
    MayBeUndefined {
        environment: Rc<Environment>,
        introduced_variable: crate::Variable,
        witness: Model,
    },
    AssumedExistence {
        environment: Rc<Environment>,
        introduced_variable: crate::Variable,
    },
    Unknown {
        environment: Option<Rc<Environment>>,
    },
    Error {
        environment: Rc<Environment>,
        error: ModelFindingError,
    },
    InconsistentAssumptions {
        max_dimension: Option<u64>,
    },
    DimensionallyInvalid {
        environment: Rc<Environment>,
        declarations: Vec<Expr<()>>,
    },
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct StepValidationData {
    pub checks: Vec<StepCheck>,
    pub max_dimension: Option<u64>,
    pub environments_exhaustive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgumentStep {
    pub sentence: Expr<()>,
    pub validation: StepValidationData,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Argument {
    pub name: String,
    pub assumptions: Vec<Expr<()>>,
    pub steps: Vec<ArgumentStep>,
    pub error: Option<ArgumentValidationError>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Arguments(pub Vec<Argument>);

impl ArgumentStep {
    fn has_counterexample(&self) -> bool {
        self.validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Counterexample { .. }))
    }
}

impl Argument {
    pub fn validate(&mut self, max_dimension: u64) -> Result<(), ArgumentValidationError> {
        self.error = None;
        for step in &mut self.steps {
            step.validation.checks.clear();
            step.validation.max_dimension = Some(max_dimension);
            step.validation.environments_exhaustive = false;
        }

        let symbolic_types = infer_symbolic_type_environment(&self.assumptions)?;
        let prepared_assumptions = self
            .assumptions
            .iter()
            .map(|expression| prepare_expression(&symbolic_types, expression, POSITIVE))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)
            .map_err(ModelFindingError::from)?;
        let prepared_positive = self
            .steps
            .iter()
            .map(|step| prepare_expression(&symbolic_types, &step.sentence, POSITIVE))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)
            .map_err(ModelFindingError::from)?;
        let prepared_negative = self
            .steps
            .iter()
            .map(|step| prepare_expression(&symbolic_types, &step.sentence, NEGATIVE))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)
            .map_err(ModelFindingError::from)?;

        let environments = match extract_prepared_environment_iterator(
            &symbolic_types,
            &prepared_assumptions,
            &[],
            max_dimension,
        ) {
            Ok(environments) => environments,
            Err(ShapeError::Unsat(_)) => {
                self.record_inconsistent_assumptions(None);
                return Ok(());
            }
            Err(ShapeError::Unknown(_)) => {
                self.record_unknown(None);
                return Ok(());
            }
            Err(error) => return Err(error.into()),
        };

        let environments_exhaustive = environments.dimension_bound_is_exhaustive();
        for step in &mut self.steps {
            step.validation.environments_exhaustive = environments_exhaustive;
        }

        let mut satisfiable_assumption_count = 0;
        let mut assumption_unknown = false;
        for environment in environments {
            let environment = match environment {
                Ok(environment) => Rc::new(environment),
                Err(ShapeError::Unknown(_)) => {
                    assumption_unknown = true;
                    self.record_unknown(None);
                    continue;
                }
                Err(error) => return Err(error.into()),
            };
            match self.validate_environment(
                Rc::clone(&environment),
                &symbolic_types,
                &prepared_assumptions,
                &prepared_positive,
                &prepared_negative,
                max_dimension,
            )? {
                EnvironmentResult::Sat => satisfiable_assumption_count += 1,
                EnvironmentResult::Unsat => {}
                EnvironmentResult::Unknown => assumption_unknown = true,
            }
            if self.steps.iter().all(ArgumentStep::has_counterexample) {
                break;
            }
        }

        if satisfiable_assumption_count == 0 && !assumption_unknown {
            self.record_inconsistent_assumptions(
                (!environments_exhaustive).then_some(max_dimension),
            );
        }
        Ok(())
    }

    fn validate_environment(
        &mut self,
        environment: Rc<Environment>,
        symbolic_types: &SymbolicTypeEnvironment,
        prepared_assumptions: &[PreparedExpression],
        prepared_positive: &[PreparedExpression],
        prepared_negative: &[PreparedExpression],
        max_dimension: u64,
    ) -> Result<EnvironmentResult, ArgumentValidationError> {
        let mut solver = Solver::new();
        assert_natural_assignment(&solver, &environment);

        let mut tracked = Vec::new();
        for (index, (assumption, prepared)) in self
            .assumptions
            .iter()
            .zip(prepared_assumptions)
            .enumerate()
        {
            let assertion = lower_prepared_boolean(&environment, prepared)?;
            assert_definitions(&solver, &assertion.side_conditions)?;
            let tracker = Bool::new_const(format!("argument_assumption_{index}"));
            solver.assert_and_track(assertion.expression, &tracker);
            tracked.push((tracker, assumption.clone()));
        }

        match solver.check() {
            SatResult::Unsat => {
                let supporting_facts = core_facts(&solver, &tracked);
                for step in &mut self.steps {
                    if !step.has_counterexample() {
                        step.validation.checks.push(StepCheck::Unsat {
                            environment: Rc::clone(&environment),
                            supporting_facts: supporting_facts.clone(),
                        });
                    }
                }
                return Ok(EnvironmentResult::Unsat);
            }
            SatResult::Unknown => {
                self.record_unknown(Some(environment));
                return Ok(EnvironmentResult::Unknown);
            }
            SatResult::Sat => {}
        }

        for index in 0..self.steps.len() {
            if self.steps[index].has_counterexample() {
                continue;
            }
            let sentence = self.steps[index].sentence.clone();
            let extensions = step_environment_extensions(
                &environment,
                symbolic_types,
                &prepared_positive[index],
                max_dimension,
            )?;
            self.steps[index].validation.environments_exhaustive &= extensions.exhaustive;
            if extensions.environments.is_empty() {
                self.steps[index]
                    .validation
                    .checks
                    .push(StepCheck::DimensionallyInvalid {
                        environment: Rc::clone(&environment),
                        declarations: concrete_declarations(symbolic_types, &environment)?,
                    });
                continue;
            }

            let mut accepted = Vec::new();
            let mut failed = false;
            for extension in extensions.environments {
                let extension = Rc::new(extension);
                let negative_assertion =
                    match lower_prepared_boolean(&extension, &prepared_negative[index]) {
                        Ok(assertion) => assertion,
                        Err(error) => {
                            self.steps[index].validation.checks.push(StepCheck::Error {
                                environment: Rc::clone(&environment),
                                error,
                            });
                            failed = true;
                            break;
                        }
                    };
                solver.push();
                assert_definitions(&solver, &negative_assertion.side_conditions)?;
                solver.assert(negative_assertion.expression.not());
                match solver.check() {
                    SatResult::Sat => {
                        let model = solver
                            .get_model()
                            .ok_or(ModelFindingError::MissingModel)
                            .and_then(|model| extract_model(&environment, symbolic_types, &model));
                        solver.pop(1);
                        self.steps[index].validation.checks.push(match model {
                            Ok(model) => StepCheck::Counterexample {
                                environment: Rc::clone(&environment),
                                model,
                            },
                            Err(error) => StepCheck::Error {
                                environment: Rc::clone(&environment),
                                error,
                            },
                        });
                        failed = true;
                        break;
                    }
                    SatResult::Unknown => {
                        solver.pop(1);
                        self.steps[index]
                            .validation
                            .checks
                            .push(StepCheck::Unknown {
                                environment: Some(Rc::clone(&environment)),
                            });
                        failed = true;
                        break;
                    }
                    SatResult::Unsat => {
                        let supporting_facts = core_facts(&solver, &tracked);
                        solver.pop(1);
                        let positive =
                            match lower_prepared_boolean(&extension, &prepared_positive[index]) {
                                Ok(assertion) => assertion,
                                Err(error) => {
                                    self.steps[index].validation.checks.push(StepCheck::Error {
                                        environment: Rc::clone(&environment),
                                        error,
                                    });
                                    failed = true;
                                    break;
                                }
                            };
                        let warnings = check_step_existence(
                            &mut solver,
                            Rc::clone(&environment),
                            symbolic_types,
                            &positive.side_conditions,
                        )?;
                        if warnings.is_empty() {
                            self.steps[index].validation.checks.push(StepCheck::Unsat {
                                environment: Rc::clone(&environment),
                                supporting_facts,
                            });
                        } else {
                            self.steps[index].validation.checks.extend(warnings);
                        }
                        accepted.push(positive);
                    }
                }
            }
            if !failed {
                let mut expressions = Vec::new();
                for assertion in &accepted {
                    assert_definitions(&solver, &assertion.side_conditions)?;
                    expressions.push(assertion.expression.clone());
                }
                track_step(
                    &mut solver,
                    index,
                    Bool::and(&expressions),
                    sentence,
                    &mut tracked,
                );
            }
        }
        Ok(EnvironmentResult::Sat)
    }

    fn record_unknown(&mut self, environment: Option<Rc<Environment>>) {
        for step in &mut self.steps {
            if !step.has_counterexample() {
                step.validation.checks.push(StepCheck::Unknown {
                    environment: environment.clone(),
                });
            }
        }
    }

    fn record_inconsistent_assumptions(&mut self, max_dimension: Option<u64>) {
        for step in &mut self.steps {
            if !step.has_counterexample() {
                step.validation
                    .checks
                    .push(StepCheck::InconsistentAssumptions { max_dimension });
            }
        }
    }
}

impl Arguments {
    pub fn validate(&mut self, max_dimension: u64) {
        for argument in &mut self.0 {
            if let Err(error) = argument.validate(max_dimension) {
                argument.error = Some(error);
            }
        }
    }
}

enum EnvironmentResult {
    Sat,
    Unsat,
    Unknown,
}

fn step_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    step: &PreparedExpression,
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let mut declarations = Vec::new();
    let mut extension_types = symbolic_types.clone();
    for parameter in base.natural_assignment.keys() {
        if let NaturalParameter::Variable(variable) = parameter {
            extension_types
                .types
                .entry(variable.clone())
                .or_insert(TypeExpr::Nat);
        }
    }
    for (parameter, value) in &base.natural_assignment {
        let expression: Expr<()> = match parameter {
            NaturalParameter::Variable(variable) => Expr::new(RawExpr::Variable(variable.clone())),
            NaturalParameter::ImplicitDimension(dimension) => {
                Expr::new(RawExpr::ImplicitDimension(*dimension))
            }
        };
        let equality = Expr::new(RawExpr::CmpChain(CmpChain {
            start: expression,
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(*value)))],
        }));
        declarations.push(
            prepare_expression(&extension_types, &equality, POSITIVE)
                .map_err(crate::to_z3::ToZ3Error::from)
                .map_err(ModelFindingError::from)?,
        );
    }
    declarations.push(step.clone());
    let iterator = match extract_prepared_environment_iterator(
        &extension_types,
        &declarations,
        &[],
        max_dimension,
    ) {
        Ok(iterator) => iterator,
        Err(ShapeError::Unsat(_)) | Err(ShapeError::InvalidTyping(_)) => {
            return Ok(StepEnvironmentExtensions {
                environments: Vec::new(),
                exhaustive: true,
            });
        }
        Err(error) => return Err(error.into()),
    };
    let exhaustive = iterator.dimension_bound_is_exhaustive();
    let environments = iterator
        .collect::<Result<Vec<_>, ShapeError>>()
        .map_err(ArgumentValidationError::from)?;
    Ok(StepEnvironmentExtensions {
        environments,
        exhaustive,
    })
}

struct StepEnvironmentExtensions {
    environments: Vec<Environment>,
    exhaustive: bool,
}

fn concrete_declarations(
    symbolic_types: &SymbolicTypeEnvironment,
    environment: &Environment,
) -> Result<Vec<Expr<()>>, ModelFindingError> {
    let mut declarations = symbolic_types
        .types
        .iter()
        .map(|(variable, ty)| {
            let ty = ty
                .concretize(environment)
                .map_err(crate::to_z3::ToZ3Error::from)?;
            Ok(Expr::new(RawExpr::Binop(
                Binop::ElementOf,
                Expr::new(RawExpr::Variable(variable.clone())),
                Expr::new(RawExpr::Type(TypeExpr::from(ty))),
            )))
        })
        .collect::<Result<Vec<_>, ModelFindingError>>()?;
    declarations.sort();
    Ok(declarations)
}

fn track_step(
    solver: &mut Solver,
    index: usize,
    assertion: Bool,
    sentence: Expr<()>,
    tracked: &mut Vec<(Bool, Expr<()>)>,
) {
    let tracker = Bool::new_const(format!("argument_step_{index}"));
    solver.assert_and_track(assertion, &tracker);
    tracked.push((tracker, sentence));
}

fn check_step_existence(
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    side_conditions: &[LoweredSideCondition],
) -> Result<Vec<StepCheck>, ModelFindingError> {
    let mut checks = Vec::new();
    for condition in side_conditions {
        match &condition.existence {
            LoweredExistence::Guaranteed => {}
            LoweredExistence::Assumed => checks.push(StepCheck::AssumedExistence {
                environment: Rc::clone(&environment),
                introduced_variable: crate::Variable::new(condition.display_name.clone()),
            }),
            LoweredExistence::Checkable(assertions) => {
                solver.push();
                for other in side_conditions {
                    if other.introduced_variable != condition.introduced_variable {
                        assert_definitions(solver, std::slice::from_ref(other))?;
                    }
                }
                for assertion in assertions {
                    solver.assert(z3_boolean(assertion)?);
                }
                let result = match solver.check() {
                    SatResult::Unsat => None,
                    SatResult::Unknown => Some(StepCheck::Unknown {
                        environment: Some(Rc::clone(&environment)),
                    }),
                    SatResult::Sat => Some(StepCheck::MayBeUndefined {
                        environment: Rc::clone(&environment),
                        introduced_variable: crate::Variable::new(condition.display_name.clone()),
                        witness: extract_model(
                            &environment,
                            symbolic_types,
                            &solver.get_model().ok_or(ModelFindingError::MissingModel)?,
                        )?,
                    }),
                };
                solver.pop(1);
                if let Some(result) = result {
                    checks.push(result);
                }
            }
        }
    }
    Ok(checks)
}

fn core_facts(solver: &Solver, tracked: &[(Bool, Expr<()>)]) -> Vec<Expr<()>> {
    let core = solver.get_unsat_core();
    tracked
        .iter()
        .filter(|(tracker, _)| core.contains(tracker))
        .map(|(_, expression)| expression.clone())
        .collect()
}

impl ToFromMd for Argument {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        assert!(
            matches!(
                children.first(),
                Some(Node::Heading(Heading { depth: 1, .. }))
            ),
            "argument must start with a level-one heading"
        );
        let name = heading_text(&children[0]);
        let assumptions_start = section_start(children, "Assumptions");
        let steps_start = section_start(children, "Steps");
        assert!(
            assumptions_start < steps_start,
            "argument sections are out of order"
        );
        let assumptions =
            parse_expression_section(&children[assumptions_start + 1..steps_start], "assumptions");
        let steps = parse_steps(&children[steps_start + 1..]);
        Self {
            name,
            assumptions,
            steps,
            error: None,
        }
    }

    fn to_md(&self) -> Node {
        let mut children = vec![heading(1, &self.name), heading(2, "Assumptions")];
        if !self.assumptions.is_empty() {
            children.push(expression_list(&self.assumptions));
        }
        children.push(heading(2, "Steps"));
        if !self.steps.is_empty() {
            children.push(step_list(self));
        }
        if let Some(error) = &self.error {
            children.push(heading(2, "Error"));
            children.push(Node::Paragraph(Paragraph {
                children: vec![Node::Text(markdown::mdast::Text {
                    value: error.to_string(),
                    position: None,
                })],
                position: None,
            }));
        }
        root(children)
    }
}

impl ToFromMd for Arguments {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        let starts: Vec<_> = children
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match node {
                Node::Heading(Heading { depth: 1, .. }) => Some(index),
                _ => None,
            })
            .collect();
        assert!(!starts.is_empty(), "argument collection is empty");
        Self(
            starts
                .iter()
                .enumerate()
                .map(|(index, start)| {
                    let end = starts.get(index + 1).copied().unwrap_or(children.len());
                    Argument::parse_md(&Node::Root(Root {
                        children: children[*start..end].to_vec(),
                        position: None,
                    }))
                })
                .collect(),
        )
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "argument collection is empty");
        root(
            self.0
                .iter()
                .flat_map(|argument| root_children(&argument.to_md()).to_vec())
                .collect(),
        )
    }
}

impl Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_md(&self.to_md()))
    }
}

impl Display for Arguments {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_md(&self.to_md()))
    }
}

fn parse_steps(nodes: &[Node]) -> Vec<ArgumentStep> {
    let [
        Node::List(List {
            children,
            ordered: true,
            ..
        }),
    ] = nodes
    else {
        panic!("expected an ordered list of argument steps")
    };
    children
        .iter()
        .map(|item| ArgumentStep {
            sentence: parse_expression_item(item),
            validation: StepValidationData::default(),
        })
        .collect()
}

fn step_list(argument: &Argument) -> Node {
    Node::List(List {
        children: argument
            .steps
            .iter()
            .map(|step| {
                let mut children = vec![Node::Paragraph(Paragraph {
                    children: vec![Node::InlineMath(InlineMath {
                        value: step.sentence.as_latex().to_string(),
                        position: None,
                    })],
                    position: None,
                })];
                if let Some(details) = step_details(argument, step) {
                    children.push(Node::Html(Html {
                        value: details,
                        position: None,
                    }));
                }
                Node::ListItem(ListItem {
                    children,
                    position: None,
                    spread: true,
                    checked: None,
                })
            })
            .collect(),
        position: None,
        ordered: true,
        start: Some(1),
        spread: true,
    })
}

fn step_details(argument: &Argument, step: &ArgumentStep) -> Option<String> {
    if let Some(StepCheck::Counterexample { model, .. }) = step
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Counterexample { .. }))
    {
        let assignments = expression_bullets(model);
        return Some(format!(
            "<details>\n<summary>❌ counterexample found</summary>\n\nThe negation of ${}$ is satisfied by:\n\n{assignments}\n</details>",
            step.sentence.as_latex()
        ));
    }
    if let Some(StepCheck::DimensionallyInvalid { declarations, .. }) = step
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::DimensionallyInvalid { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ dimensionally invalid</summary>\n\nThis step is not dimensionally meaningful in the following environment:\n\n{}\n</details>",
            expression_bullets(declarations)
        ));
    }
    if let Some(StepCheck::Error { error, .. }) = step
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Error { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Unsupported step</summary>\n\n{error}\n</details>"
        ));
    }
    let existence_warnings: Vec<_> = step
        .validation
        .checks
        .iter()
        .filter(|check| {
            matches!(
                check,
                StepCheck::MayBeUndefined { .. } | StepCheck::AssumedExistence { .. }
            )
        })
        .collect();
    if !existence_warnings.is_empty() {
        let mut messages = Vec::new();
        for warning in existence_warnings {
            match warning {
                StepCheck::MayBeUndefined {
                    introduced_variable,
                    witness,
                    ..
                } => messages.push(format!(
                    "The expression ${}$ may be undefined. For example:\n\n{}",
                    introduced_variable.name,
                    expression_bullets(witness)
                )),
                StepCheck::AssumedExistence {
                    introduced_variable,
                    ..
                } => messages.push(format!(
                    "The existence of ${}$ was assumed without checking.",
                    introduced_variable.name
                )),
                _ => unreachable!(),
            }
        }
        return Some(format!(
            "<details>\n<summary>⚠️ conditional</summary>\n\n{}\n</details>",
            messages.join("\n\n")
        ));
    }
    if step
        .validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::Unknown { .. }))
    {
        return Some(
            "<details>\n<summary>Inconclusive</summary>\n\nZ3 could not determine whether a counterexample exists in every environment tried.\n</details>"
                .to_owned(),
        );
    }
    if let Some(StepCheck::InconsistentAssumptions { max_dimension }) = step
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InconsistentAssumptions { .. }))
    {
        let message = match max_dimension {
            Some(max_dimension) => {
                format!("The assumptions are inconsistent up to dimension {max_dimension}.")
            }
            None => "The assumptions are inconsistent.".to_owned(),
        };
        return Some(format!(
            "<details>\n<summary>Inconsistent assumptions</summary>\n\n{message}\n</details>"
        ));
    }
    if step.validation.checks.is_empty() {
        return None;
    }

    let present: BTreeSet<_> = step
        .validation
        .checks
        .iter()
        .filter_map(|check| match check {
            StepCheck::Unsat {
                supporting_facts, ..
            } => Some(supporting_facts),
            _ => None,
        })
        .flatten()
        .cloned()
        .collect();
    let supporting_facts: Vec<_> = argument
        .assumptions
        .iter()
        .chain(argument.steps.iter().map(|step| &step.sentence))
        .filter(|expression| present.contains(*expression))
        .cloned()
        .collect();
    let explanation = if supporting_facts.is_empty() {
        "No premises seemed necessary to show this.".to_owned()
    } else if step.validation.environments_exhaustive {
        format!(
            "This follows from the following facts:\n\n{}",
            expression_bullets(&supporting_facts)
        )
    } else {
        format!(
            "This may follow from the following facts:\n\n{}",
            expression_bullets(&supporting_facts)
        )
    };
    if step.validation.environments_exhaustive {
        Some(format!(
            "<details>\n<summary>✅ verified</summary>\n\n{explanation}\n</details>"
        ))
    } else {
        let max_dimension = step
            .validation
            .max_dimension
            .unwrap_or_else(|| panic!("validated step is missing its maximum dimension"));
        Some(format!(
            "<details>\n<summary>✅ likely</summary>\n\nNo counterexamples found up to a maximum dimension of {max_dimension}.\n\n{explanation}\n</details>"
        ))
    }
}

fn expression_bullets(expressions: &[Expr<()>]) -> String {
    expressions
        .iter()
        .map(|expression| format!("- ${}$", expression.as_latex()))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{Argument, Arguments, StepCheck, ToFromMd};

    const ARGUMENT: &str = r#"# Scalar argument

## Assumptions

- $x \in \mathbb{R}$

## Steps

1. $x = x$
2. $x = 0$
3. $x = x$"#;

    #[test]
    fn pending_argument_round_trips() {
        let argument = Argument::parse_str(ARGUMENT);
        assert_eq!(argument.to_string(), ARGUMENT);
        assert!(
            argument
                .steps
                .iter()
                .all(|step| step.validation.checks.is_empty())
        );
    }

    #[test]
    fn validates_all_steps_incrementally_for_one_environment() {
        let mut argument = Argument::parse_str(ARGUMENT);
        argument.validate(0).unwrap();

        let StepCheck::Unsat {
            environment: first_environment,
            ..
        } = &argument.steps[0].validation.checks[0]
        else {
            panic!("first step should be likely")
        };
        let StepCheck::Counterexample {
            environment: second_environment,
            ..
        } = &argument.steps[1].validation.checks[0]
        else {
            panic!("second step should have a counterexample")
        };
        let StepCheck::Unsat {
            environment: third_environment,
            ..
        } = &argument.steps[2].validation.checks[0]
        else {
            panic!("third step should be likely")
        };
        assert!(Rc::ptr_eq(first_environment, second_environment));
        assert!(Rc::ptr_eq(second_environment, third_environment));

        let rendered = argument.to_string();
        assert!(rendered.contains("✅ verified"));
        assert!(rendered.contains("❌ counterexample found"));
        assert!(!rendered.contains("maximum dimension of 0"));
    }

    #[test]
    fn lowers_a_logic_chain_negatively_then_tracks_it_positively() {
        let mut argument = Argument::parse_str(
            r#"# Logic chain

## Assumptions

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $z \in \mathbb{R}$
- $x = 0$
- $y = 0$
- $z = 0$

## Steps

1. $x = 0 \iff y = 0 \implies z = 0$
2. $z = 0$"#,
        );

        argument.validate(0).unwrap();

        assert!(matches!(
            argument.steps[0].validation.checks[0],
            StepCheck::Unsat { .. }
        ));
        assert!(matches!(
            argument.steps[1].validation.checks[0],
            StepCheck::Unsat { .. }
        ));
    }

    #[test]
    fn step_errors_are_recorded_and_do_not_stop_later_steps() {
        let mut argument = Argument::parse_str(
            r#"# Unsupported step

## Assumptions

## Steps

1. $1$
2. $1 = 1$"#,
        );
        argument.validate(0).unwrap();
        assert!(matches!(
            argument.steps[0].validation.checks[0],
            StepCheck::Error { .. }
        ));
        assert!(matches!(
            argument.steps[1].validation.checks[0],
            StepCheck::Unsat { .. }
        ));
    }

    #[test]
    fn inconsistent_assumptions_are_recorded_on_every_step() {
        let mut argument = Argument::parse_str(
            r#"# Inconsistent

## Assumptions

- $n < 0$

## Steps

1. $n = n$"#,
        );
        argument.validate(2).unwrap();
        assert!(matches!(
            argument.steps[0].validation.checks[0],
            StepCheck::InconsistentAssumptions {
                max_dimension: None
            }
        ));
    }

    #[test]
    fn verified_step_accumulates_supporting_facts_from_unsat_cores() {
        let mut argument = Argument::parse_str(
            r#"# Supported

## Assumptions

- $x \in \mathbb{R}$
- $x = 0$

## Steps

1. $x \le 0$"#,
        );
        argument.validate(0).unwrap();
        let StepCheck::Unsat {
            supporting_facts, ..
        } = &argument.steps[0].validation.checks[0]
        else {
            panic!("step should be likely")
        };
        assert!(supporting_facts.contains(&argument.assumptions[1]));
        assert!(
            argument
                .to_string()
                .contains("This follows from the following facts:")
        );
    }

    #[test]
    fn value_level_inconsistency_reflects_dimension_exhaustiveness() {
        let mut argument = Argument::parse_str(
            r#"# Dimensionless inconsistency

## Assumptions

- $x \in \mathbb{R}$
- $x = 0$
- $x = 1$

## Steps

1. $x = x$"#,
        );
        argument.validate(3).unwrap();
        assert!(matches!(
            argument.steps[0].validation.checks.last(),
            Some(StepCheck::InconsistentAssumptions {
                max_dimension: None
            })
        ));

        let mut argument = Argument::parse_str(
            r#"# Bounded inconsistency

## Assumptions

- $A = A$
- $A \ne A$

## Steps

1. $A = A$"#,
        );
        argument.validate(3).unwrap();
        assert!(
            argument.steps[0]
                .validation
                .checks
                .iter()
                .any(|check| matches!(
                    check,
                    StepCheck::InconsistentAssumptions {
                        max_dimension: Some(3)
                    }
                ))
        );
    }

    #[test]
    fn verified_requires_base_and_step_local_exhaustiveness() {
        let mut fixed = Argument::parse_str(
            r#"# Fixed

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Steps

1. $A = A$"#,
        );
        fixed.validate(2).unwrap();
        let rendered = fixed.to_string();
        assert!(rendered.contains("✅ verified"));
        assert!(!rendered.contains("maximum dimension"));

        let mut symbolic = Argument::parse_str(
            r#"# Symbolic

## Assumptions

- $A = A$

## Steps

1. $A = A$"#,
        );
        symbolic.validate(2).unwrap();
        assert!(symbolic.to_string().contains("✅ likely"));

        let mut step_local = Argument::parse_str(
            r#"# Step local

## Assumptions

## Steps

1. $I = I$"#,
        );
        step_local.validate(2).unwrap();
        assert!(step_local.to_string().contains("✅ likely"));
    }

    #[test]
    #[should_panic(expected = "expression list item must contain one paragraph")]
    fn annotated_output_is_not_parseable_as_input() {
        let mut argument = Argument::parse_str(ARGUMENT);
        argument.validate(0).unwrap();
        Argument::parse_str(&argument.to_string());
    }

    #[test]
    fn collection_records_argument_errors_and_continues() {
        let invalid = Argument::parse_str(
            r#"# Invalid

## Assumptions

- $A \in \mathbb{R}^{n p}$

## Steps

1. $A = A$"#,
        );
        let valid = Argument::parse_str(ARGUMENT);
        let mut arguments = Arguments(vec![invalid, valid]);
        arguments.validate(0);
        assert!(arguments.0[0].error.is_some());
        assert!(arguments.0[1].error.is_none());
        assert!(!arguments.0[1].steps[0].validation.checks.is_empty());
    }
}
