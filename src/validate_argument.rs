use std::{
    collections::{BTreeSet, HashSet},
    error::Error,
    fmt::{self, Display},
    rc::Rc,
};

use markdown::mdast::{Heading, Html, InlineMath, List, ListItem, Node, Paragraph, Root};
use z3::{SatResult, Solver, ast::Bool};

pub use crate::model_finding::{ModelFindingError, ToFromMd};
use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Logic, LogicChain, Model, NaturalParameter,
    RawExpr, TypeExpr, Variable,
    enumerable_envspec::{
        ShapeError, extract_prepared_environment_iterator, infer_symbolic_type_environment,
    },
    model_finding::{
        assert_definitions, assert_natural_assignment, expression_list, extract_model, heading,
        heading_text, lower_prepared_boolean, parse_expression_item, render_md, root,
        root_children, z3_boolean,
    },
    preprocessing::{PreparedExpression, prepare_expression},
    to_z3::{LoweredExistence, LoweredSideCondition, ToZ3Error},
    type_resolver::{SymbolicTypeEnvironment, TypeError},
    visit::Visit,
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
    InconsistentGivens {
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
    pub(crate) givens_feasible: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgumentStep {
    pub sentence: Expr<()>,
    pub validation: StepValidationData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    pub givens: Vec<Expr<()>>,
    pub conclusion: Expr<()>,
    pub steps: Vec<ArgumentItem>,
    pub validation: StepValidationData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgumentItem {
    Sentence(ArgumentStep),
    Goal(Goal),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Argument {
    pub name: String,
    pub root: Goal,
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

impl Goal {
    fn has_counterexample(&self) -> bool {
        self.validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Counterexample { .. }))
    }

    fn reset(&mut self, max_dimension: u64) {
        reset_validation(&mut self.validation, max_dimension);
        for item in &mut self.steps {
            match item {
                ArgumentItem::Sentence(step) => {
                    reset_validation(&mut step.validation, max_dimension)
                }
                ArgumentItem::Goal(goal) => goal.reset(max_dimension),
            }
        }
    }
}

fn reset_validation(validation: &mut StepValidationData, max_dimension: u64) {
    validation.checks.clear();
    validation.max_dimension = Some(max_dimension);
    validation.environments_exhaustive = false;
    validation.givens_feasible = false;
}

impl Argument {
    pub fn validate(&mut self, max_dimension: u64) -> Result<(), ArgumentValidationError> {
        self.error = None;
        self.root.reset(max_dimension);

        let symbolic_types = infer_symbolic_type_environment(&self.root.givens)?;
        let prepared_givens = self
            .root
            .givens
            .iter()
            .map(|expression| prepare_expression(&symbolic_types, expression, POSITIVE))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)
            .map_err(ModelFindingError::from)?;

        let environments = match extract_prepared_environment_iterator(
            &symbolic_types,
            &prepared_givens,
            &[],
            max_dimension,
        ) {
            Ok(environments) => environments,
            Err(ShapeError::Unsat(_)) => {
                self.root
                    .validation
                    .checks
                    .push(StepCheck::InconsistentGivens {
                        max_dimension: None,
                    });
                return Ok(());
            }
            Err(ShapeError::Unknown(_)) => {
                self.root
                    .validation
                    .checks
                    .push(StepCheck::Unknown { environment: None });
                return Ok(());
            }
            Err(error) => return Err(error.into()),
        };

        let environments_exhaustive = environments.dimension_bound_is_exhaustive();
        set_exhaustive(&mut self.root, environments_exhaustive);

        let mut satisfiable_given_count = 0;
        let mut given_unknown = false;
        let mut run = ValidationRun {
            max_dimension,
            next_tracker: 0,
        };
        for environment in environments {
            let environment = match environment {
                Ok(environment) => Rc::new(environment),
                Err(ShapeError::Unknown(_)) => {
                    given_unknown = true;
                    self.root
                        .validation
                        .checks
                        .push(StepCheck::Unknown { environment: None });
                    continue;
                }
                Err(error) => return Err(error.into()),
            };
            let mut solver = Solver::new();
            assert_natural_assignment(&solver, &environment);
            let mut tracked = Vec::new();
            for (given, prepared) in self.root.givens.iter().zip(&prepared_givens) {
                let assertion = lower_prepared_boolean(&environment, prepared)?;
                assert_definitions(&solver, &assertion.side_conditions)?;
                let tracker = fresh_tracker(&mut run.next_tracker);
                solver.assert_and_track(assertion.expression, &tracker);
                tracked.push((tracker, given.clone()));
            }
            match solver.check() {
                SatResult::Sat => {
                    satisfiable_given_count += 1;
                    self.root.validation.givens_feasible = true;
                    let mut scoped_statements = Vec::new();
                    validate_goal_contents(
                        &mut self.root,
                        &mut solver,
                        Rc::clone(&environment),
                        &symbolic_types,
                        &mut tracked,
                        &mut scoped_statements,
                        &mut run,
                    )?;
                }
                SatResult::Unknown => {
                    given_unknown = true;
                    self.root.validation.checks.push(StepCheck::Unknown {
                        environment: Some(environment),
                    });
                }
                SatResult::Unsat => {}
            }
        }

        if satisfiable_given_count == 0 && !given_unknown {
            self.root
                .validation
                .checks
                .push(StepCheck::InconsistentGivens {
                    max_dimension: (!environments_exhaustive).then_some(max_dimension),
                });
        }
        Ok(())
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

#[derive(Default)]
struct ClaimResult {
    assertions: Vec<crate::model_finding::LoweredBoolean>,
    validated: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ScopedStatement {
    introduced_variables: BTreeSet<Variable>,
    givens: Vec<Expr<()>>,
    conclusion: Expr<()>,
}

struct GoalExport {
    statement: ScopedStatement,
    assertions: Vec<crate::model_finding::LoweredBoolean>,
}

struct ValidationRun {
    max_dimension: u64,
    next_tracker: usize,
}

fn set_exhaustive(goal: &mut Goal, exhaustive: bool) {
    goal.validation.environments_exhaustive = exhaustive;
    for item in &mut goal.steps {
        match item {
            ArgumentItem::Sentence(step) => step.validation.environments_exhaustive = exhaustive,
            ArgumentItem::Goal(goal) => set_exhaustive(goal, exhaustive),
        }
    }
}

fn and_exhaustive(goal: &mut Goal, exhaustive: bool) {
    goal.validation.environments_exhaustive &= exhaustive;
    for item in &mut goal.steps {
        match item {
            ArgumentItem::Sentence(step) => step.validation.environments_exhaustive &= exhaustive,
            ArgumentItem::Goal(goal) => and_exhaustive(goal, exhaustive),
        }
    }
}

fn fresh_tracker(next_tracker: &mut usize) -> Bool {
    let tracker = Bool::new_const(format!("argument_fact_{}", *next_tracker));
    *next_tracker += 1;
    tracker
}

fn track_assertions(
    solver: &mut Solver,
    assertions: &[crate::model_finding::LoweredBoolean],
    sentence: Expr<()>,
    tracked: &mut Vec<(Bool, Expr<()>)>,
    next_tracker: &mut usize,
) -> Result<(), ModelFindingError> {
    let mut expressions = Vec::new();
    for assertion in assertions {
        assert_definitions(solver, &assertion.side_conditions)?;
        expressions.push(assertion.expression.clone());
    }
    let tracker = fresh_tracker(next_tracker);
    solver.assert_and_track(Bool::and(&expressions), &tracker);
    tracked.push((tracker, sentence));
    Ok(())
}

fn validate_goal_contents(
    goal: &mut Goal,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    tracked: &mut Vec<(Bool, Expr<()>)>,
    scoped_statements: &mut Vec<ScopedStatement>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    for item in &mut goal.steps {
        match item {
            ArgumentItem::Sentence(step) => {
                if step.has_counterexample() {
                    continue;
                }
                let result = validate_claim(
                    &step.sentence,
                    &mut step.validation,
                    solver,
                    Rc::clone(&environment),
                    symbolic_types,
                    tracked,
                    run.max_dimension,
                )?;
                if result.validated {
                    track_assertions(
                        solver,
                        &result.assertions,
                        step.sentence.clone(),
                        tracked,
                        &mut run.next_tracker,
                    )?;
                }
            }
            ArgumentItem::Goal(child) => {
                let export = validate_nested_goal(
                    child,
                    solver,
                    Rc::clone(&environment),
                    symbolic_types,
                    tracked,
                    scoped_statements,
                    run,
                )?;
                if let Some(export) = export {
                    scoped_statements.push(export.statement);
                    if !export.assertions.is_empty() {
                        track_assertions(
                            solver,
                            &export.assertions,
                            child.conclusion.clone(),
                            tracked,
                            &mut run.next_tracker,
                        )?;
                    }
                }
            }
        }
    }

    if goal.has_counterexample() {
        return Ok(ClaimResult::default());
    }
    validate_claim(
        &goal.conclusion,
        &mut goal.validation,
        solver,
        environment,
        symbolic_types,
        tracked,
        run.max_dimension,
    )
}

fn validate_nested_goal(
    goal: &mut Goal,
    solver: &mut Solver,
    parent_environment: Rc<Environment>,
    parent_types: &SymbolicTypeEnvironment,
    parent_tracked: &[(Bool, Expr<()>)],
    parent_scoped_statements: &[ScopedStatement],
    run: &mut ValidationRun,
) -> Result<Option<GoalExport>, ArgumentValidationError> {
    if goal.has_counterexample() {
        return Ok(None);
    }

    let (symbolic_types, introduced_variables) =
        match extend_symbolic_types(parent_types, &goal.givens) {
            Ok(result) => result,
            Err(ArgumentValidationError::Shape(error)) => {
                goal.validation.checks.push(StepCheck::Error {
                    environment: parent_environment,
                    error: ModelFindingError::from(error),
                });
                return Ok(None);
            }
            Err(error) => return Err(error),
        };
    let prepared_givens = match goal
        .givens
        .iter()
        .map(|given| prepare_expression(&symbolic_types, given, POSITIVE))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)
    {
        Ok(givens) => givens,
        Err(error) => {
            goal.validation.checks.push(StepCheck::Error {
                environment: parent_environment,
                error,
            });
            return Ok(None);
        }
    };

    let extensions = goal_environment_extensions(
        &parent_environment,
        &symbolic_types,
        &prepared_givens,
        run.max_dimension,
    )?;
    and_exhaustive(goal, extensions.exhaustive);
    if extensions.environments.is_empty() {
        record_inconsistent_givens(goal, extensions.exhaustive, run.max_dimension);
        return Ok(None);
    }

    let implication = introduced_variables
        .is_empty()
        .then(|| scoped_statement_expression(&goal.givens, &goal.conclusion));
    let prepared_implication = implication
        .as_ref()
        .map(|expression| prepare_expression(&symbolic_types, expression, POSITIVE))
        .transpose()
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)?;

    let mut feasible = 0;
    let mut all_validated = true;
    let mut exported = Vec::new();
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut tracked = parent_tracked.to_vec();
        let mut scoped_statements = parent_scoped_statements.to_vec();
        for (given, prepared) in goal.givens.iter().zip(&prepared_givens) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            tracked.push((tracker, given.clone()));
        }
        match solver.check() {
            SatResult::Sat => {
                feasible += 1;
                let result = validate_goal_contents(
                    goal,
                    solver,
                    Rc::clone(&extension),
                    &symbolic_types,
                    &mut tracked,
                    &mut scoped_statements,
                    run,
                )?;
                all_validated &= result.validated;
                if result.validated
                    && let Some(prepared) = &prepared_implication
                {
                    exported.push(lower_prepared_boolean(&extension, prepared)?);
                }
            }
            SatResult::Unknown => {
                all_validated = false;
                goal.validation.checks.push(StepCheck::Unknown {
                    environment: Some(Rc::clone(&extension)),
                });
            }
            SatResult::Unsat => {}
        }
        solver.pop(1);
    }

    if feasible == 0 {
        record_inconsistent_givens(goal, extensions.exhaustive, run.max_dimension);
        return Ok(None);
    }
    goal.validation.givens_feasible = true;
    goal.validation
        .checks
        .retain(|check| !matches!(check, StepCheck::InconsistentGivens { .. }));
    if all_validated {
        Ok(Some(GoalExport {
            statement: ScopedStatement {
                introduced_variables,
                givens: goal.givens.clone(),
                conclusion: goal.conclusion.clone(),
            },
            assertions: exported,
        }))
    } else {
        Ok(None)
    }
}

fn record_inconsistent_givens(goal: &mut Goal, exhaustive: bool, max_dimension: u64) {
    if !goal.validation.givens_feasible
        && !goal
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::InconsistentGivens { .. }))
    {
        goal.validation.checks.push(StepCheck::InconsistentGivens {
            max_dimension: (!exhaustive).then_some(max_dimension),
        });
    }
}

fn validate_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    tracked: &[(Bool, Expr<()>)],
    max_dimension: u64,
) -> Result<ClaimResult, ArgumentValidationError> {
    if let Err(error) = ensure_expression_bound(sentence, symbolic_types) {
        validation
            .checks
            .push(StepCheck::Error { environment, error });
        return Ok(ClaimResult::default());
    }
    let positive = match prepare_expression(symbolic_types, sentence, POSITIVE) {
        Ok(prepared) => prepared,
        Err(error) => {
            validation.checks.push(StepCheck::Error {
                environment,
                error: ModelFindingError::from(ToZ3Error::from(error)),
            });
            return Ok(ClaimResult::default());
        }
    };
    let negative = match prepare_expression(symbolic_types, sentence, NEGATIVE) {
        Ok(prepared) => prepared,
        Err(error) => {
            validation.checks.push(StepCheck::Error {
                environment,
                error: ModelFindingError::from(ToZ3Error::from(error)),
            });
            return Ok(ClaimResult::default());
        }
    };
    let extensions =
        expression_environment_extensions(&environment, symbolic_types, &positive, max_dimension)?;
    validation.environments_exhaustive &= extensions.exhaustive;
    if extensions.environments.is_empty() {
        validation.checks.push(StepCheck::DimensionallyInvalid {
            environment: Rc::clone(&environment),
            declarations: concrete_declarations(symbolic_types, &environment)?,
        });
        return Ok(ClaimResult::default());
    }

    let mut accepted = Vec::new();
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        let negative_assertion = match lower_prepared_boolean(&extension, &negative) {
            Ok(assertion) => assertion,
            Err(error) => {
                validation.checks.push(StepCheck::Error {
                    environment: Rc::clone(&extension),
                    error,
                });
                return Ok(ClaimResult::default());
            }
        };
        solver.push();
        assert_natural_assignment(solver, &extension);
        assert_definitions(solver, &negative_assertion.side_conditions)?;
        solver.assert(negative_assertion.expression.not());
        match solver.check() {
            SatResult::Sat => {
                let model = solver
                    .get_model()
                    .ok_or(ModelFindingError::MissingModel)
                    .and_then(|model| extract_model(&extension, symbolic_types, &model));
                solver.pop(1);
                validation.checks.push(match model {
                    Ok(model) => StepCheck::Counterexample {
                        environment: extension,
                        model,
                    },
                    Err(error) => StepCheck::Error {
                        environment: extension,
                        error,
                    },
                });
                return Ok(ClaimResult::default());
            }
            SatResult::Unknown => {
                solver.pop(1);
                validation.checks.push(StepCheck::Unknown {
                    environment: Some(extension),
                });
                return Ok(ClaimResult::default());
            }
            SatResult::Unsat => {
                let supporting_facts = core_facts(solver, tracked);
                solver.pop(1);
                solver.push();
                assert_natural_assignment(solver, &extension);
                let positive = lower_prepared_boolean(&extension, &positive)?;
                let warnings = check_step_existence(
                    solver,
                    Rc::clone(&extension),
                    symbolic_types,
                    &positive.side_conditions,
                )?;
                solver.pop(1);
                if warnings.is_empty() {
                    validation.checks.push(StepCheck::Unsat {
                        environment: extension,
                        supporting_facts,
                    });
                } else {
                    validation.checks.extend(warnings);
                }
                accepted.push(positive);
            }
        }
    }
    Ok(ClaimResult {
        assertions: accepted,
        validated: true,
    })
}

fn scoped_statement_expression(givens: &[Expr<()>], conclusion: &Expr<()>) -> Expr<()> {
    if givens.is_empty() {
        return conclusion.clone();
    }
    let antecedent = if let [given] = givens {
        given.clone()
    } else {
        Expr::new(RawExpr::Finop(Finop::And, givens.to_vec()))
    };
    Expr::new(RawExpr::LogicChain(LogicChain {
        start: antecedent,
        assertions: vec![(Logic::Imp, conclusion.clone())],
    }))
}

fn extend_symbolic_types(
    parent: &SymbolicTypeEnvironment,
    givens: &[Expr<()>],
) -> Result<(SymbolicTypeEnvironment, BTreeSet<Variable>), ArgumentValidationError> {
    let variables = free_variables(givens.iter());
    let introduced = variables
        .iter()
        .filter(|variable| !parent.types.contains_key(*variable))
        .cloned()
        .collect::<BTreeSet<_>>();
    let inferred = infer_symbolic_type_environment(givens)?;
    let mut extended = parent.clone();
    for variable in &introduced {
        let ty = inferred.types.get(variable).cloned().ok_or_else(|| {
            ShapeError::InvalidTyping(format!(
                "missing inferred type for introduced variable {}",
                variable.z3_name()
            ))
        })?;
        extended.types.insert(variable.clone(), ty);
    }
    Ok((extended, introduced))
}

fn ensure_expression_bound(
    expression: &Expr<()>,
    types: &SymbolicTypeEnvironment,
) -> Result<(), ModelFindingError> {
    if let Some(variable) = free_variables(std::iter::once(expression))
        .into_iter()
        .find(|variable| !types.types.contains_key(variable))
    {
        return Err(ModelFindingError::from(ToZ3Error::from(
            TypeError::MissingType(variable),
        )));
    }
    Ok(())
}

struct FreeVariableCollector {
    variables: BTreeSet<Variable>,
    bound: HashSet<Variable>,
}

impl Visit<()> for FreeVariableCollector {
    fn visit_variable(&mut self, variable: &Variable) {
        if !self.bound.contains(variable) {
            self.variables.insert(variable.clone());
        }
    }

    fn visit_raw_expr_seqop(
        &mut self,
        _op: &crate::SeqOp,
        range: &crate::Range<()>,
        body: &Expr<()>,
    ) {
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
        assert!(
            self.bound.insert(range.index_variable.clone()),
            "sequence binder shadows an active binder"
        );
        self.visit_expr(body);
        self.bound.remove(&range.index_variable);
    }
}

fn free_variables<'a>(expressions: impl Iterator<Item = &'a Expr<()>>) -> BTreeSet<Variable> {
    let mut collector = FreeVariableCollector {
        variables: BTreeSet::new(),
        bound: HashSet::new(),
    };
    for expression in expressions {
        collector.visit_expr(expression);
    }
    collector.variables
}

fn fixed_assignment_declarations(
    base: &Environment,
    extension_types: &SymbolicTypeEnvironment,
) -> Result<Vec<PreparedExpression>, ArgumentValidationError> {
    let mut extension_types = extension_types.clone();
    for parameter in base.natural_assignment.keys() {
        if let NaturalParameter::Variable(variable) = parameter {
            extension_types
                .types
                .entry(variable.clone())
                .or_insert(TypeExpr::Nat);
        }
    }
    base.natural_assignment
        .iter()
        .map(|(parameter, value)| {
            let expression: Expr<()> = match parameter {
                NaturalParameter::Variable(variable) => {
                    Expr::new(RawExpr::Variable(variable.clone()))
                }
                NaturalParameter::ImplicitDimension(dimension) => {
                    Expr::new(RawExpr::ImplicitDimension(*dimension))
                }
            };
            let equality = Expr::new(RawExpr::CmpChain(CmpChain {
                start: expression,
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(*value)))],
            }));
            prepare_expression(&extension_types, &equality, POSITIVE)
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)
                .map_err(ArgumentValidationError::from)
        })
        .collect()
}

fn goal_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    givens: &[PreparedExpression],
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let assumptions = declarations
        .iter()
        .chain(givens)
        .cloned()
        .collect::<Vec<_>>();
    let iterator = match extract_prepared_environment_iterator(
        symbolic_types,
        &assumptions,
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
    let environments = iterator.collect::<Result<Vec<_>, _>>()?;
    Ok(StepEnvironmentExtensions {
        environments,
        exhaustive,
    })
}

fn expression_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    step: &PreparedExpression,
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let iterator = match extract_prepared_environment_iterator(
        symbolic_types,
        &declarations,
        std::slice::from_ref(step),
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
        let root = parse_goal(&children[1..]);
        Self {
            name,
            root,
            error: None,
        }
    }

    fn to_md(&self) -> Node {
        let expressions = argument_expressions(self);
        let mut children = vec![heading(1, &self.name)];
        children.extend(goal_nodes(&self.root, &expressions));
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

fn parse_goal(nodes: &[Node]) -> Goal {
    let mut index = 0;
    let givens = if paragraph_is_label(nodes.get(index), "Given:") {
        index += 1;
        let Node::List(List {
            children,
            ordered: false,
            ..
        }) = nodes
            .get(index)
            .unwrap_or_else(|| panic!("Given must be followed by an unordered expression list"))
        else {
            panic!("Given must be followed by an unordered expression list")
        };
        assert!(!children.is_empty(), "Given list must not be empty");
        index += 1;
        children.iter().map(parse_expression_item).collect()
    } else {
        Vec::new()
    };
    let conclusion = parse_wts(
        nodes
            .get(index)
            .unwrap_or_else(|| panic!("goal must contain WTS")),
    );
    index += 1;
    let steps = if let Some(node) = nodes.get(index) {
        index += 1;
        parse_argument_items(node)
    } else {
        Vec::new()
    };
    assert_eq!(index, nodes.len(), "unexpected content after goal");
    Goal {
        givens,
        conclusion,
        steps,
        validation: StepValidationData::default(),
    }
}

fn paragraph_is_label(node: Option<&Node>, expected: &str) -> bool {
    matches!(
        node,
        Some(Node::Paragraph(Paragraph { children, .. }))
            if matches!(children.as_slice(), [Node::Text(text)] if text.value == expected)
    )
}

fn parse_wts(node: &Node) -> Expr<()> {
    let Node::Paragraph(Paragraph { children, .. }) = node else {
        panic!("WTS must be a paragraph")
    };
    let [Node::Text(label), Node::InlineMath(math)] = children.as_slice() else {
        panic!("WTS must contain exactly one inline TeX expression")
    };
    assert_eq!(label.value, "WTS ", "goal paragraph must start with WTS");
    let parsed = ratex_parser::parse(&math.value).expect("invalid TeX in WTS expression");
    crate::from_tex::expr(&parsed).expect("unsupported TeX in WTS expression")
}

fn parse_argument_items(node: &Node) -> Vec<ArgumentItem> {
    let Node::List(List {
        children,
        ordered: true,
        ..
    }) = node
    else {
        panic!("goal body must be an ordered list")
    };
    children.iter().map(parse_argument_item).collect()
}

fn parse_argument_item(node: &Node) -> ArgumentItem {
    let Node::ListItem(ListItem { children, .. }) = node else {
        panic!("argument item must be a list item")
    };
    if matches!(children.first(), Some(Node::Paragraph(Paragraph { children, .. })) if matches!(children.first(), Some(Node::InlineMath(_))))
    {
        return ArgumentItem::Sentence(ArgumentStep {
            sentence: parse_expression_item(node),
            validation: StepValidationData::default(),
        });
    }
    ArgumentItem::Goal(parse_goal(children))
}

fn goal_nodes(goal: &Goal, expressions: &[Expr<()>]) -> Vec<Node> {
    let mut nodes = Vec::new();
    if !goal.givens.is_empty() {
        nodes.push(text_paragraph("Given:"));
        nodes.push(expression_list(&goal.givens));
    }
    nodes.push(Node::Paragraph(Paragraph {
        children: vec![
            Node::Text(markdown::mdast::Text {
                value: "WTS ".to_owned(),
                position: None,
            }),
            Node::InlineMath(InlineMath {
                value: goal.conclusion.as_latex().to_string(),
                position: None,
            }),
        ],
        position: None,
    }));
    if !goal.steps.is_empty() {
        nodes.push(argument_item_list(&goal.steps, expressions));
    }
    if let Some(details) = validation_details(&goal.conclusion, &goal.validation, expressions) {
        nodes.push(Node::Html(Html {
            value: details,
            position: None,
        }));
    }
    nodes
}

fn text_paragraph(value: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![Node::Text(markdown::mdast::Text {
            value: value.to_owned(),
            position: None,
        })],
        position: None,
    })
}

fn argument_item_list(items: &[ArgumentItem], expressions: &[Expr<()>]) -> Node {
    Node::List(List {
        children: items
            .iter()
            .map(|item| {
                let children = match item {
                    ArgumentItem::Sentence(step) => {
                        let mut children = vec![Node::Paragraph(Paragraph {
                            children: vec![Node::InlineMath(InlineMath {
                                value: step.sentence.as_latex().to_string(),
                                position: None,
                            })],
                            position: None,
                        })];
                        if let Some(details) =
                            validation_details(&step.sentence, &step.validation, expressions)
                        {
                            children.push(Node::Html(Html {
                                value: details,
                                position: None,
                            }));
                        }
                        children
                    }
                    ArgumentItem::Goal(goal) => goal_nodes(goal, expressions),
                };
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

fn validation_details(
    sentence: &Expr<()>,
    validation: &StepValidationData,
    expressions: &[Expr<()>],
) -> Option<String> {
    if let Some(StepCheck::Counterexample { model, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Counterexample { .. }))
    {
        let assignments = expression_bullets(model);
        return Some(format!(
            "<details>\n<summary>❌ counterexample found</summary>\n\nThe negation of ${}$ is satisfied by:\n\n{assignments}\n</details>",
            sentence.as_latex()
        ));
    }
    if let Some(StepCheck::DimensionallyInvalid { declarations, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::DimensionallyInvalid { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ dimensionally invalid</summary>\n\nThis step is not dimensionally meaningful in the following environment:\n\n{}\n</details>",
            expression_bullets(declarations)
        ));
    }
    if let Some(StepCheck::Error { error, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Error { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Unsupported step</summary>\n\n{error}\n</details>"
        ));
    }
    let existence_warnings: Vec<_> = validation
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
    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::Unknown { .. }))
    {
        return Some(
            "<details>\n<summary>Inconclusive</summary>\n\nZ3 could not determine whether a counterexample exists in every environment tried.\n</details>"
                .to_owned(),
        );
    }
    if let Some(StepCheck::InconsistentGivens { max_dimension }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InconsistentGivens { .. }))
    {
        let message = match max_dimension {
            Some(max_dimension) => {
                format!("The givens are inconsistent up to dimension {max_dimension}.")
            }
            None => "The givens are inconsistent.".to_owned(),
        };
        return Some(format!(
            "<details>\n<summary>Inconsistent givens</summary>\n\n{message}\n</details>"
        ));
    }
    if validation.checks.is_empty() {
        return None;
    }

    let present: BTreeSet<_> = validation
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
    let supporting_facts: Vec<_> = expressions
        .iter()
        .filter(|expression| present.contains(*expression))
        .cloned()
        .collect();
    let explanation = if supporting_facts.is_empty() {
        "No premises seemed necessary to show this.".to_owned()
    } else if validation.environments_exhaustive {
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
    if validation.environments_exhaustive {
        Some(format!(
            "<details>\n<summary>✅ verified</summary>\n\n{explanation}\n</details>"
        ))
    } else {
        let max_dimension = validation
            .max_dimension
            .unwrap_or_else(|| panic!("validated step is missing its maximum dimension"));
        Some(format!(
            "<details>\n<summary>✅ likely</summary>\n\nNo counterexamples found up to a maximum dimension of {max_dimension}.\n\n{explanation}\n</details>"
        ))
    }
}

fn argument_expressions(argument: &Argument) -> Vec<Expr<()>> {
    fn collect(goal: &Goal, expressions: &mut Vec<Expr<()>>) {
        expressions.extend(goal.givens.iter().cloned());
        for item in &goal.steps {
            match item {
                ArgumentItem::Sentence(step) => expressions.push(step.sentence.clone()),
                ArgumentItem::Goal(goal) => collect(goal, expressions),
            }
        }
        expressions.push(goal.conclusion.clone());
    }

    let mut expressions = Vec::new();
    collect(&argument.root, &mut expressions);
    expressions
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
    use super::{Argument, ArgumentItem, Arguments, StepCheck, ToFromMd};

    const ARGUMENT: &str = r#"# Scalar argument

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $x = x$
2. $x = 0$"#;

    fn sentence(argument: &Argument, index: usize) -> &super::ArgumentStep {
        let ArgumentItem::Sentence(step) = &argument.root.steps[index] else {
            panic!("expected a sentence")
        };
        step
    }

    #[test]
    fn pending_argument_round_trips() {
        let argument = Argument::parse_str(ARGUMENT);
        assert_eq!(argument.to_string(), ARGUMENT);
        assert!(argument.root.validation.checks.is_empty());
        assert!(argument.root.steps.iter().all(|item| match item {
            ArgumentItem::Sentence(step) => step.validation.checks.is_empty(),
            ArgumentItem::Goal(goal) => goal.validation.checks.is_empty(),
        }));
    }

    #[test]
    fn failed_children_do_not_invalidate_the_goal() {
        let mut argument = Argument::parse_str(ARGUMENT);
        argument.validate(0).unwrap();

        assert!(matches!(
            sentence(&argument, 0).validation.checks[0],
            StepCheck::Unsat { .. }
        ));
        assert!(matches!(
            sentence(&argument, 1).validation.checks[0],
            StepCheck::Counterexample { .. }
        ));
        assert!(matches!(
            argument.root.validation.checks[0],
            StepCheck::Unsat { .. }
        ));
    }

    #[test]
    fn nested_goals_round_trip_and_validate_locally() {
        let input = r#"# Nested

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. WTS $x = x$

   1. $x = 0$
   2. $x = x$
2. Given:

   - $y \in \mathbb{R}$

   WTS $y = y$"#;
        let mut argument = Argument::parse_str(input);
        assert_eq!(argument.to_string(), input);
        argument.validate(0).unwrap();

        let ArgumentItem::Goal(first) = &argument.root.steps[0] else {
            panic!("expected nested goal")
        };
        assert!(matches!(
            first.validation.checks[0],
            StepCheck::Unsat { .. }
        ));
        assert!(matches!(
            &first.steps[0],
            ArgumentItem::Sentence(step)
                if matches!(step.validation.checks[0], StepCheck::Counterexample { .. })
        ));

        let ArgumentItem::Goal(second) = &argument.root.steps[1] else {
            panic!("expected scoped goal")
        };
        assert!(matches!(
            second.validation.checks[0],
            StepCheck::Unsat { .. }
        ));
    }

    #[test]
    fn inconsistent_givens_are_reported_on_the_goal_only() {
        let mut argument = Argument::parse_str(
            r#"# Inconsistent

Given:

- $n < 0$

WTS $n = n$

1. $n = 0$"#,
        );
        argument.validate(2).unwrap();
        assert!(matches!(
            argument.root.validation.checks[0],
            StepCheck::InconsistentGivens {
                max_dimension: None
            }
        ));
        assert!(sentence(&argument, 0).validation.checks.is_empty());
    }

    #[test]
    fn unbound_child_errors_are_localized() {
        let mut argument = Argument::parse_str(
            r#"# Unbound child

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $y = y$
2. $x = x$"#,
        );
        argument.validate(0).unwrap();
        assert!(matches!(
            sentence(&argument, 0).validation.checks[0],
            StepCheck::Error { .. }
        ));
        assert!(matches!(
            sentence(&argument, 1).validation.checks[0],
            StepCheck::Unsat { .. }
        ));
        assert!(matches!(
            argument.root.validation.checks[0],
            StepCheck::Unsat { .. }
        ));
    }

    #[test]
    fn local_givens_do_not_escape_their_goal() {
        let mut argument = Argument::parse_str(
            r#"# Scoped givens

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. Given:

   - $x = 0$

   WTS $x \le 0$
2. $x = 0$"#,
        );
        argument.validate(0).unwrap();
        let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
            panic!("expected nested goal")
        };
        assert!(matches!(goal.validation.checks[0], StepCheck::Unsat { .. }));
        assert!(matches!(
            sentence(&argument, 1).validation.checks[0],
            StepCheck::Counterexample { .. }
        ));
    }

    #[test]
    fn partially_feasible_givens_are_not_reported_as_vacuous() {
        let mut argument = Argument::parse_str(
            r#"# Partial givens

Given:

- $A = A$

WTS $A = A$

1. Given:

   - $A \in \mathbb{R}^{2 \times 2}$

   WTS $A = A$"#,
        );
        argument.validate(2).unwrap();
        let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
            panic!("expected nested goal")
        };
        assert!(
            goal.validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::Unsat { .. }))
        );
        assert!(
            !goal
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::InconsistentGivens { .. }))
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

Given:

- $A \in \mathbb{R}^{n p}$

WTS $A = A$"#,
        );
        let valid = Argument::parse_str(ARGUMENT);
        let mut arguments = Arguments(vec![invalid, valid]);
        arguments.validate(0);
        assert!(arguments.0[0].error.is_some());
        assert!(arguments.0[1].error.is_none());
        assert!(!arguments.0[1].root.validation.checks.is_empty());
    }
}
