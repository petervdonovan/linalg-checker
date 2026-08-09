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
    Binop, Environment, Expr, Model, RawExpr, Type, TypeExpr,
    enumerable_envspec::{ShapeError, extract_environment_iterator_with_context},
    model_finding::{
        assert_environment_equalities, expression_list, extract_model, heading, heading_text,
        lower_boolean, parse_expression_item, parse_expression_section, render_md, root,
        root_children, section_start,
    },
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
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct StepValidationData {
    pub checks: Vec<StepCheck>,
    pub max_dimension: Option<u64>,
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
        }

        let environments = match extract_environment_iterator_with_context(
            self.assumptions.iter().cloned(),
            self.steps.iter().map(|step| step.sentence.clone()),
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
            match self.validate_environment(Rc::clone(&environment))? {
                EnvironmentResult::Sat => satisfiable_assumption_count += 1,
                EnvironmentResult::Unsat => {}
                EnvironmentResult::Unknown => assumption_unknown = true,
            }
        }

        if satisfiable_assumption_count == 0 && !assumption_unknown {
            self.record_inconsistent_assumptions(Some(max_dimension));
        }
        Ok(())
    }

    fn validate_environment(
        &mut self,
        environment: Rc<Environment>,
    ) -> Result<EnvironmentResult, ArgumentValidationError> {
        let mut solver = Solver::new();
        assert_natural_constraints(&mut solver, &environment)?;
        assert_environment_equalities(&solver, &environment)?;

        let mut tracked = Vec::new();
        for assumption in &self.assumptions {
            let assertion = lower_boolean(&environment, assumption)?;
            let tracker = Bool::fresh_const("argument_assumption");
            solver.assert_and_track(assertion, &tracker);
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
            let assertion = match lower_boolean(&environment, &sentence) {
                Ok(assertion) => assertion,
                Err(error) => {
                    self.steps[index].validation.checks.push(StepCheck::Error {
                        environment: Rc::clone(&environment),
                        error,
                    });
                    continue;
                }
            };

            solver.push();
            solver.assert(assertion.not());
            match solver.check() {
                SatResult::Sat => {
                    let result = solver
                        .get_model()
                        .ok_or(ModelFindingError::MissingModel)
                        .and_then(|model| extract_model(&environment, &model));
                    solver.pop(1);
                    match result {
                        Ok(model) => {
                            self.steps[index]
                                .validation
                                .checks
                                .push(StepCheck::Counterexample {
                                    environment: Rc::clone(&environment),
                                    model,
                                })
                        }
                        Err(error) => self.steps[index].validation.checks.push(StepCheck::Error {
                            environment: Rc::clone(&environment),
                            error,
                        }),
                    }
                }
                SatResult::Unsat => {
                    let supporting_facts = core_facts(&solver, &tracked);
                    solver.pop(1);
                    self.steps[index].validation.checks.push(StepCheck::Unsat {
                        environment: Rc::clone(&environment),
                        supporting_facts,
                    });
                    track_step(&mut solver, assertion, sentence, &mut tracked);
                }
                SatResult::Unknown => {
                    solver.pop(1);
                    self.steps[index]
                        .validation
                        .checks
                        .push(StepCheck::Unknown {
                            environment: Some(Rc::clone(&environment)),
                        });
                    track_step(&mut solver, assertion, sentence, &mut tracked);
                }
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

fn assert_natural_constraints(
    solver: &mut Solver,
    environment: &Environment,
) -> Result<(), ModelFindingError> {
    for (variable, ty) in &environment.types {
        if !matches!(ty, Type::Nat) {
            continue;
        }
        let type_assertion = Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(variable.clone())),
            Expr::new(RawExpr::Type(TypeExpr::from(ty.clone()))),
        ));
        solver.assert(lower_boolean(environment, &type_assertion)?);
    }
    Ok(())
}

fn track_step(
    solver: &mut Solver,
    assertion: Bool,
    sentence: Expr<()>,
    tracked: &mut Vec<(Bool, Expr<()>)>,
) {
    let tracker = Bool::fresh_const("argument_step");
    solver.assert_and_track(assertion, &tracker);
    tracked.push((tracker, sentence));
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
        "No tracked premises appeared in the unsatisfiable cores.".to_owned()
    } else {
        format!(
            "This may follow from the following facts:\n\n{}",
            expression_bullets(&supporting_facts)
        )
    };
    let max_dimension = step
        .validation
        .max_dimension
        .unwrap_or_else(|| panic!("validated step is missing its maximum dimension"));
    Some(format!(
        "<details>\n<summary>✅ likely</summary>\n\nNo counterexamples found up to a maximum dimension of {max_dimension}.\n\n{explanation}\n</details>"
    ))
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
        assert!(rendered.contains("✅ likely"));
        assert!(rendered.contains("❌ counterexample found"));
        assert!(rendered.contains("maximum dimension of 0"));
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
    fn likely_step_accumulates_supporting_facts_from_unsat_cores() {
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
                .contains("This may follow from the following facts:")
        );
    }

    #[test]
    fn value_level_inconsistency_is_bounded() {
        let mut argument = Argument::parse_str(
            r#"# Bounded inconsistency

## Assumptions

- $x \in \mathbb{R}$
- $x = 0$
- $x = 1$

## Steps

1. $x = x$"#,
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
