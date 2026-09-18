use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt::{self, Display},
    rc::Rc,
};

use z3::{SatResult, Solver, ast::Bool};

pub use crate::model_finding::{ModelFindingError, ToFromMd};
use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Logic, LogicChain, Model, NaturalParameter,
    RawExpr, TypeExpr, Variable,
    enumerable_envspec::{
        ShapeError, extract_prepared_environment_iterator,
        extract_prepared_environment_iterator_with_required_context,
        infer_symbolic_type_environment,
    },
    formula::{contains_quantifier, free_variables, is_quantifier, substitute_free_variable},
    model_finding::{
        assert_definitions, assert_natural_assignment, expression_list, extract_model, heading,
        heading_text, lower_prepared_boolean, parse_expression_item, render_md, root,
        root_children, z3_boolean,
    },
    preprocessing::{
        PreparedExpression, prepare_expression, prepare_expression_with_premises, prepare_givens,
    },
    to_z3::{LoweredExistence, LoweredSideCondition, ToZ3Error},
    type_resolver::{MaybeTyped, SymbolicTypeEnvironment, TypeError},
    unification::Unifier,
    visit_mut::VisitContext,
};

use crate::deep_clone::deep_clone;

const POSITIVE: VisitContext = VisitContext {
    logical_polarity: true,
    active_ranges: Vec::new(),
};
const NEGATIVE: VisitContext = VisitContext {
    logical_polarity: false,
    active_ranges: Vec::new(),
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
    TacticEstablished,
    IncompleteSubgoals {
        expected: Vec<Expr<()>>,
    },
    QuestionableQuantifier {
        premises: Vec<Expr<()>>,
    },
    EstablishedByFact {
        fact: Expr<()>,
    },
    ExistentialWitness {
        assignments: Vec<(Variable, Expr<()>)>,
        supporting_facts: Vec<Expr<()>>,
    },
    ExistentialElimination {
        fact: Expr<()>,
        assignments: Vec<(Variable, Variable)>,
    },
    InvalidExistentialElimination {
        message: String,
    },
    QuantifierInconclusive {
        message: String,
    },
    VacuousQuantifier,
    InvalidTactic {
        message: String,
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

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tactic {
    Induction { variable: Variable },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    pub givens: Vec<Expr<()>>,
    pub conclusion: Expr<()>,
    pub tactic: Option<Tactic>,
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

        if self.root.tactic.is_some() {
            set_exhaustive(&mut self.root, true);
            self.root.validation.givens_feasible = true;
            let environment = Rc::new(Environment::default());
            let mut solver = Solver::new();
            let mut tracked = Vec::new();
            let mut scoped_statements = Vec::new();
            let mut run = ValidationRun {
                max_dimension,
                next_tracker: 0,
                givens: Vec::new(),
            };
            validate_goal_contents(
                &mut self.root,
                &mut solver,
                environment,
                &SymbolicTypeEnvironment::default(),
                &mut tracked,
                &mut scoped_statements,
                &mut run,
            )?;
            return Ok(());
        }

        let analyzed =
            match analyze_goal_givens(&SymbolicTypeEnvironment::default(), &self.root.givens, None)
            {
                Ok(analyzed) => analyzed,
                Err(message) => {
                    self.root
                        .validation
                        .checks
                        .push(StepCheck::QuantifierInconclusive { message });
                    return Ok(());
                }
            };
        if !analyzed.questionable.is_empty() {
            self.root
                .validation
                .checks
                .push(StepCheck::QuestionableQuantifier {
                    premises: analyzed.questionable.clone(),
                });
        }
        let symbolic_types = analyzed.symbolic_types;
        let ordinary_givens = analyzed.ordinary;
        let retained_givens = analyzed.retained;
        let prepared_givens = prepare_givens(&symbolic_types, &ordinary_givens, &[], max_dimension)
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
            givens: prepared_givens.clone(),
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
            for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
                let assertion = lower_prepared_boolean(&environment, prepared)?;
                assert_definitions(&solver, &assertion.side_conditions)?;
                let tracker = fresh_tracker(&mut run.next_tracker);
                solver.assert_and_track(assertion.expression, &tracker);
                tracked.push(TrackedFact {
                    tracker,
                    sentence: given.clone(),
                    alternatives: prepared.expression.meta.alternatives().to_vec(),
                });
            }
            match solver.check() {
                SatResult::Sat => {
                    satisfiable_given_count += 1;
                    self.root.validation.givens_feasible = true;
                    let mut scoped_statements = retained_givens.clone();
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
    retained: Vec<Expr<()>>,
    introduced_types: BTreeMap<Variable, TypeExpr<()>>,
    alternatives: Vec<Expr<()>>,
    validated: bool,
}

struct GoalExport {
    statement: Expr<()>,
    assertions: Vec<crate::model_finding::LoweredBoolean>,
}

struct ValidationRun {
    /// Prepared lexical givens only; accepted proof steps never enter this scope.
    givens: Vec<PreparedExpression>,
    max_dimension: u64,
    next_tracker: usize,
}

#[derive(Clone)]
struct TrackedFact {
    tracker: Bool,
    sentence: Expr<()>,
    alternatives: Vec<Expr<()>>,
}

#[derive(Clone, Copy)]
struct ProofContext<'a> {
    tracked: &'a [TrackedFact],
    retained: &'a [Expr<()>],
}

struct ParentGoalScope<'a> {
    symbolic_types: &'a SymbolicTypeEnvironment,
    tracked: &'a [TrackedFact],
    scoped_statements: &'a [Expr<()>],
    forced_natural: Option<(&'a Variable, u64)>,
}

mod induction;
use induction::{
    InductionObligations, infer_induction_start, natural_lower_bound, validate_tactic_fallback,
};
fn scoped_goal_expression(givens: &[Expr<()>], conclusion: &Expr<()>) -> Expr<()> {
    if givens.is_empty() {
        return deep_clone(conclusion);
    }
    let mut expressions = givens.iter().map(deep_clone).collect::<Vec<_>>();
    expressions.push(deep_clone(conclusion));
    Expr::new(RawExpr::Finop(Finop::Forall, expressions))
}

fn exported_goal_expression(
    introduced_variables: &BTreeSet<Variable>,
    givens: &[Expr<()>],
    conclusion: &Expr<()>,
) -> Expr<()> {
    if introduced_variables.is_empty() {
        scoped_statement_expression(givens, conclusion)
    } else {
        scoped_goal_expression(givens, conclusion)
    }
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
    alternatives: Vec<Expr<()>>,
    tracked: &mut Vec<TrackedFact>,
    next_tracker: &mut usize,
) -> Result<(), ModelFindingError> {
    let mut expressions = Vec::new();
    for assertion in assertions {
        assert_definitions(solver, &assertion.side_conditions)?;
        expressions.push(assertion.expression.clone());
    }
    let tracker = fresh_tracker(next_tracker);
    solver.assert_and_track(Bool::and(&expressions), &tracker);
    tracked.push(TrackedFact {
        tracker,
        sentence,
        alternatives,
    });
    Ok(())
}

fn validate_goal_contents(
    goal: &mut Goal,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    tracked: &mut Vec<TrackedFact>,
    scoped_statements: &mut Vec<Expr<()>>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let induction = match &goal.tactic {
        Some(Tactic::Induction { variable }) => {
            if symbolic_types.types.contains_key(variable) {
                goal.validation.checks.push(StepCheck::InvalidTactic {
                    message: format!(
                        "the induction variable {} is already active; rename it",
                        variable.z3_name()
                    ),
                });
                None
            } else if !free_variables(goal.givens.iter().chain(std::iter::once(&goal.conclusion)))
                .contains(variable)
            {
                goal.validation.checks.push(StepCheck::InvalidTactic {
                    message: format!(
                        "the induction variable {} does not occur freely in the goal",
                        variable.z3_name()
                    ),
                });
                None
            } else {
                match infer_induction_start(
                    goal,
                    variable,
                    &environment,
                    symbolic_types,
                    &run.givens,
                    run.max_dimension,
                )? {
                    Some(start) => Some((start, InductionObligations::new(goal, variable, start))),
                    None => {
                        goal.validation.checks.push(StepCheck::InvalidTactic {
                            message: format!(
                                "no admissible starting value for {} was found up to {}",
                                variable.z3_name(),
                                run.max_dimension
                            ),
                        });
                        None
                    }
                }
            }
        }
        None => None,
    };
    let tactic_is_invalid = goal.tactic.is_some() && induction.is_none();
    let mut base_valid = false;
    let mut base_exhaustive = false;
    let mut step_valid = false;
    let mut step_exhaustive = false;
    let mut proof_types = symbolic_types.clone();
    let mut existential_locals = BTreeSet::new();

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
                    &proof_types,
                    ProofContext {
                        tracked,
                        retained: scoped_statements,
                    },
                    run,
                )?;
                if result.validated {
                    for (variable, ty) in &result.introduced_types {
                        proof_types.types.insert(variable.clone(), ty.clone());
                        existential_locals.insert(variable.clone());
                    }
                    if !result.assertions.is_empty() {
                        track_assertions(
                            solver,
                            &result.assertions,
                            step.sentence.clone(),
                            result.alternatives,
                            tracked,
                            &mut run.next_tracker,
                        )?;
                    }
                    scoped_statements.extend(result.retained);
                }
            }
            ArgumentItem::Goal(child) => {
                let is_base = induction
                    .as_ref()
                    .is_some_and(|(_, obligations)| obligations.matches_base(child));
                let is_step = induction
                    .as_ref()
                    .is_some_and(|(_, obligations)| obligations.matches_step(child));
                let forced_natural = is_step.then(|| {
                    let Tactic::Induction { variable } = goal.tactic.as_ref().unwrap();
                    (variable, induction.as_ref().unwrap().0)
                });
                let export = validate_nested_goal(
                    child,
                    solver,
                    Rc::clone(&environment),
                    ParentGoalScope {
                        symbolic_types: &proof_types,
                        tracked,
                        scoped_statements,
                        forced_natural,
                    },
                    run,
                )?;
                if export.is_some() {
                    if is_base {
                        base_valid = true;
                        base_exhaustive |= child.validation.environments_exhaustive;
                    }
                    if is_step {
                        step_valid = true;
                        step_exhaustive |= child.validation.environments_exhaustive;
                    }
                }
                if let Some(export) = export {
                    scoped_statements.push(export.statement);
                    if !export.assertions.is_empty() {
                        track_assertions(
                            solver,
                            &export.assertions,
                            child.conclusion.clone(),
                            Vec::new(),
                            tracked,
                            &mut run.next_tracker,
                        )?;
                    }
                }
            }
        }
    }

    if tactic_is_invalid {
        return Ok(ClaimResult::default());
    }
    if let Some((_, obligations)) = &induction {
        if base_valid && step_valid {
            goal.validation.environments_exhaustive &= base_exhaustive && step_exhaustive;
            goal.validation.checks.push(StepCheck::TacticEstablished);
            return Ok(ClaimResult {
                assertions: Vec::new(),
                retained: vec![deep_clone(&goal.conclusion)],
                introduced_types: BTreeMap::new(),
                alternatives: Vec::new(),
                validated: true,
            });
        }
        if !goal
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::IncompleteSubgoals { .. }))
        {
            let mut expected = Vec::new();
            if !base_valid {
                expected.push(deep_clone(&obligations.base));
            }
            if !step_valid {
                expected.push(deep_clone(&obligations.step));
            }
            goal.validation
                .checks
                .push(StepCheck::IncompleteSubgoals { expected });
        }
    }

    if goal.has_counterexample() {
        return Ok(ClaimResult::default());
    }
    if goal.tactic.is_some() {
        return validate_tactic_fallback(
            goal,
            solver,
            environment,
            &proof_types,
            tracked,
            scoped_statements,
            run,
        );
    }
    if free_variables(std::iter::once(&goal.conclusion))
        .iter()
        .any(|variable| existential_locals.contains(variable))
    {
        goal.validation
            .checks
            .push(StepCheck::InvalidExistentialElimination {
                message: "an existential witness cannot occur freely in the goal conclusion"
                    .to_owned(),
            });
        return Ok(ClaimResult::default());
    }
    validate_claim(
        &goal.conclusion,
        &mut goal.validation,
        solver,
        environment,
        &proof_types,
        ProofContext {
            tracked,
            retained: scoped_statements,
        },
        run,
    )
}

fn validate_nested_goal(
    goal: &mut Goal,
    solver: &mut Solver,
    parent_environment: Rc<Environment>,
    parent: ParentGoalScope<'_>,
    run: &mut ValidationRun,
) -> Result<Option<GoalExport>, ArgumentValidationError> {
    if goal.has_counterexample() {
        return Ok(None);
    }

    if goal.tactic.is_some() {
        let introduced_variables =
            free_variables(goal.givens.iter().chain(std::iter::once(&goal.conclusion)))
                .into_iter()
                .filter(|variable| !parent.symbolic_types.types.contains_key(variable))
                .collect();
        let mut tracked = parent.tracked.to_vec();
        let mut scoped_statements = parent.scoped_statements.to_vec();
        let result = validate_goal_contents(
            goal,
            solver,
            Rc::clone(&parent_environment),
            parent.symbolic_types,
            &mut tracked,
            &mut scoped_statements,
            run,
        )?;
        return Ok(result.validated.then(|| GoalExport {
            statement: exported_goal_expression(
                &introduced_variables,
                &goal.givens,
                &goal.conclusion,
            ),
            assertions: Vec::new(),
        }));
    }

    let analyzed = match analyze_goal_givens(
        parent.symbolic_types,
        &goal.givens,
        parent.forced_natural.map(|(variable, _)| variable),
    ) {
        Ok(analyzed) => analyzed,
        Err(message) => {
            goal.validation
                .checks
                .push(StepCheck::QuantifierInconclusive { message });
            return Ok(None);
        }
    };
    if !analyzed.questionable.is_empty()
        && !goal
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::QuestionableQuantifier { .. }))
    {
        goal.validation
            .checks
            .push(StepCheck::QuestionableQuantifier {
                premises: analyzed.questionable.clone(),
            });
    }
    let ordinary_givens = analyzed.ordinary;
    let symbolic_types = analyzed.symbolic_types;
    let introduced_variables = analyzed.introduced;
    let retained_givens = analyzed.retained;
    let prepared_givens = match prepare_givens(
        &symbolic_types,
        &ordinary_givens,
        &run.givens,
        run.max_dimension,
    )
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

    let forced_lower_bound = parent
        .forced_natural
        .map(|(variable, start)| natural_lower_bound(variable, start))
        .map(|bound| {
            prepare_expression(&symbolic_types, &bound, POSITIVE)
                .map(|prepared| (bound, prepared))
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)
        })
        .transpose()?;
    let mut environment_givens = prepared_givens.clone();
    if let Some((_, prepared)) = &forced_lower_bound {
        environment_givens.push(prepared.clone());
    }

    let prepared_implication =
        if introduced_variables.is_empty() && !goal.givens.iter().any(is_quantifier) {
            let mut scope = run.givens.clone();
            scope.extend(prepared_givens.iter().cloned());
            let conclusion = prepare_expression_with_premises(
                &symbolic_types,
                &goal.conclusion,
                POSITIVE,
                &scope,
                run.max_dimension,
            )
            .map_err(ModelFindingError::from_type);
            // The normal claim check records preparation failures locally.
            conclusion
                .ok()
                .map(|conclusion| conclusion.under_givens(&prepared_givens))
        } else {
            None
        };
    let implication_context = prepared_implication.as_slice();
    let extensions = goal_environment_extensions(
        &parent_environment,
        &symbolic_types,
        &environment_givens,
        implication_context,
        run.max_dimension,
    )?;
    and_exhaustive(goal, extensions.exhaustive);
    if extensions.environments.is_empty() {
        record_inconsistent_givens(goal, extensions.exhaustive, run.max_dimension);
        return Ok(None);
    }

    let mut feasible = 0;
    let mut all_validated = true;
    let mut exported = Vec::new();
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut tracked = parent.tracked.to_vec();
        let mut scoped_statements = parent.scoped_statements.to_vec();
        scoped_statements.extend(retained_givens.iter().cloned());
        for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            tracked.push(TrackedFact {
                tracker,
                sentence: given.clone(),
                alternatives: prepared.expression.meta.alternatives().to_vec(),
            });
        }
        if let Some((_, prepared)) = &forced_lower_bound {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            solver.assert(assertion.expression);
        }
        match solver.check() {
            SatResult::Sat => {
                feasible += 1;
                let scope_len = run.givens.len();
                run.givens.extend(prepared_givens.iter().cloned());
                let result = validate_goal_contents(
                    goal,
                    solver,
                    Rc::clone(&extension),
                    &symbolic_types,
                    &mut tracked,
                    &mut scoped_statements,
                    run,
                );
                run.givens.truncate(scope_len);
                let result = result?;
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
            statement: exported_goal_expression(
                &introduced_variables,
                &goal.givens,
                &goal.conclusion,
            ),
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

fn existential_payload(spec: &quantifier::QuantifierSpec) -> Expr<()> {
    let mut expressions = spec
        .premises
        .iter()
        .filter(|premise| !spec.is_binder_declaration(premise))
        .cloned()
        .collect::<Vec<_>>();
    expressions.push(spec.body.clone());
    if expressions.len() == 1 {
        expressions.pop().unwrap()
    } else {
        Expr::new(RawExpr::Finop(Finop::And, expressions))
    }
}

fn try_existential_elimination(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    environment: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    proof: ProofContext<'_>,
    run: &ValidationRun,
) -> Result<Option<ClaimResult>, ArgumentValidationError> {
    let unbound = free_variables(std::iter::once(sentence))
        .into_iter()
        .filter(|variable| !symbolic_types.types.contains_key(variable))
        .collect::<BTreeSet<_>>();
    if unbound.is_empty() {
        return Ok(None);
    }
    let accessible = symbolic_types
        .types
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    for fact in proof.tracked {
        for alternative in &fact.alternatives {
            let Ok(spec) = analyze_quantifier(alternative, symbolic_types) else {
                continue;
            };
            if !matches!(spec.kind, quantifier::QuantifierKind::Exists) {
                continue;
            }
            let payload = existential_payload(&spec);
            let Some(unifier) = crate::formula::conjunction_views(&payload)
                .into_iter()
                .find_map(|pattern| {
                    let mut unifier = Unifier {
                        metavariables: &spec.introduced,
                        assignments: BTreeMap::new(),
                        pattern_accessible: accessible
                            .iter()
                            .chain(spec.introduced.iter())
                            .cloned()
                            .collect(),
                        candidate_accessible: accessible.clone(),
                        pattern_bound: BTreeSet::new(),
                        candidate_bound: BTreeSet::new(),
                        bound_forward: BTreeMap::new(),
                        bound_reverse: BTreeMap::new(),
                        nonce_pairs: BTreeSet::new(),
                    };
                    (unifier.expression(pattern, sentence)
                        && spec
                            .introduced
                            .iter()
                            .all(|variable| unifier.assignments.contains_key(variable)))
                    .then_some(unifier)
                })
            else {
                continue;
            };
            let mut introduced_types = BTreeMap::new();
            let mut assignments = Vec::new();
            let mut assigned_variables = BTreeSet::new();
            let mut valid = true;
            for binder in &spec.introduced {
                let Some(RawExpr::Variable(candidate)) = unifier
                    .assignments
                    .get(binder)
                    .map(|expression| &expression.raw)
                else {
                    valid = false;
                    break;
                };
                if !unbound.contains(candidate) || !assigned_variables.insert(candidate.clone()) {
                    valid = false;
                    break;
                }
                let Some(ty) = spec.types.types.get(binder).cloned() else {
                    valid = false;
                    break;
                };
                introduced_types.insert(candidate.clone(), ty);
                assignments.push((binder.clone(), candidate.clone()));
            }
            if !valid || assigned_variables != unbound {
                continue;
            }
            let mut extended = symbolic_types.clone();
            extended.types.extend(introduced_types.clone());
            let prepared = prepare_expression_with_premises(
                &extended,
                sentence,
                POSITIVE,
                &run.givens,
                run.max_dimension,
            )
            .map_err(ModelFindingError::from_type)?;
            let lowered = lower_prepared_boolean(environment, &prepared)?;
            validation.checks.push(StepCheck::ExistentialElimination {
                fact: fact.sentence.clone(),
                assignments,
            });
            return Ok(Some(ClaimResult {
                assertions: vec![lowered],
                retained: Vec::new(),
                introduced_types,
                alternatives: prepared.expression.meta.alternatives().to_vec(),
                validated: true,
            }));
        }
    }
    Ok(None)
}

fn validate_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    if let Some(result) = try_existential_elimination(
        sentence,
        validation,
        &environment,
        symbolic_types,
        proof,
        run,
    )? {
        return Ok(result);
    }
    if is_quantifier(sentence) {
        return validate_quantified_claim(
            sentence,
            validation,
            solver,
            environment,
            symbolic_types,
            proof,
            run,
        );
    }
    if contains_quantifier(sentence) {
        validation.checks.push(StepCheck::QuantifierInconclusive {
            message: "quantifiers embedded beneath another operator are unsupported".to_owned(),
        });
        return Ok(ClaimResult::default());
    }
    validate_ordinary_claim(
        sentence,
        validation,
        solver,
        environment,
        symbolic_types,
        proof.tracked,
        run,
    )
}

fn validate_ordinary_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    tracked: &[TrackedFact],
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    if let Err(error) = ensure_expression_bound(sentence, symbolic_types) {
        validation
            .checks
            .push(StepCheck::Error { environment, error });
        return Ok(ClaimResult::default());
    }
    let positive = match prepare_expression_with_premises(
        symbolic_types,
        sentence,
        POSITIVE,
        &run.givens,
        run.max_dimension,
    ) {
        Ok(prepared) => prepared,
        Err(error) => {
            validation.checks.push(StepCheck::Error {
                environment,
                error: ModelFindingError::from(ToZ3Error::from(error)),
            });
            return Ok(ClaimResult::default());
        }
    };
    let negative = match prepare_expression_with_premises(
        symbolic_types,
        sentence,
        NEGATIVE,
        &run.givens,
        run.max_dimension,
    ) {
        Ok(prepared) => prepared,
        Err(error) => {
            validation.checks.push(StepCheck::Error {
                environment,
                error: ModelFindingError::from(ToZ3Error::from(error)),
            });
            return Ok(ClaimResult::default());
        }
    };
    let extensions = expression_environment_extensions(
        &environment,
        symbolic_types,
        &[positive.clone(), negative.clone()],
        run.max_dimension,
    )?;
    validation.environments_exhaustive &= extensions.exhaustive;
    if extensions.environments.is_empty() {
        validation.checks.push(StepCheck::DimensionallyInvalid {
            environment: Rc::clone(&environment),
            declarations: concrete_declarations(symbolic_types, &environment)?,
        });
        return Ok(ClaimResult::default());
    }

    let facts = proof_facts(tracked, &[]);
    let alternative_witness =
        positive
            .expression
            .meta
            .alternatives()
            .iter()
            .find_map(|alternative| {
                let spec = analyze_quantifier(alternative, symbolic_types).ok()?;
                if !matches!(spec.kind, quantifier::QuantifierKind::Exists) {
                    return None;
                }
                find_existential_witness(&spec, symbolic_types, &environment, &facts)
            });
    if let Some(witness) = alternative_witness {
        let mut accepted = Vec::new();
        for extension in extensions.environments {
            accepted.push(lower_prepared_boolean(&extension, &positive)?);
        }
        validation.checks.push(StepCheck::ExistentialWitness {
            assignments: witness.assignments.into_iter().collect(),
            supporting_facts: witness.supporting_facts,
        });
        return Ok(ClaimResult {
            assertions: accepted,
            retained: Vec::new(),
            introduced_types: BTreeMap::new(),
            alternatives: positive.expression.meta.alternatives().to_vec(),
            validated: true,
        });
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
        retained: Vec::new(),
        introduced_types: BTreeMap::new(),
        alternatives: positive.expression.meta.alternatives().to_vec(),
        validated: true,
    })
}

mod quantifier;
use quantifier::{
    analyze_quantifier, find_existential_witness, proof_facts, validate_quantified_claim,
};

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

mod environment;
use environment::{
    analyze_goal_givens, check_step_existence, concrete_declarations, core_facts,
    ensure_expression_bound, expression_environment_extensions, extend_symbolic_types,
    fixed_assignment_declarations, goal_environment_extensions, quantifier_environment_extensions,
};

mod markdown;
#[cfg(test)]
mod tests;
