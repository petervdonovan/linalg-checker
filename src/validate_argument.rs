use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
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
        ShapeError, extract_prepared_environment_iterator,
        extract_prepared_environment_iterator_with_required_context,
        infer_symbolic_type_environment,
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
    visit_mut::{self, VisitContext, VisitMut},
};

use crate::deep_clone::deep_clone;

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
        let prepared_givens = ordinary_givens
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
            for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
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
    validated: bool,
}

struct GoalExport {
    statement: Expr<()>,
    assertions: Vec<crate::model_finding::LoweredBoolean>,
}

struct ValidationRun {
    max_dimension: u64,
    next_tracker: usize,
}

#[derive(Clone, Copy)]
struct ProofContext<'a> {
    tracked: &'a [(Bool, Expr<()>)],
    retained: &'a [Expr<()>],
}

struct ParentGoalScope<'a> {
    symbolic_types: &'a SymbolicTypeEnvironment,
    tracked: &'a [(Bool, Expr<()>)],
    scoped_statements: &'a [Expr<()>],
    forced_natural: Option<(&'a Variable, u64)>,
}

struct InductionObligations {
    base: Expr<()>,
    step: Expr<()>,
}

impl InductionObligations {
    fn new(goal: &Goal, variable: &Variable, start: u64) -> Self {
        let base_value = Expr::new(RawExpr::NatLiteral(start));
        let variable_expression = Expr::new(RawExpr::Variable(variable.clone()));
        let successor = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                variable_expression.clone(),
                Expr::new(RawExpr::NatLiteral(1)),
            ],
        ));
        let base_givens = goal
            .givens
            .iter()
            .map(|given| substitute_free_variable(given, variable, &base_value))
            .collect::<Vec<_>>();
        let base_conclusion = substitute_free_variable(&goal.conclusion, variable, &base_value);
        let hypothesis = scoped_goal_expression(&goal.givens, &goal.conclusion);
        let mut step_givens = vec![hypothesis];
        step_givens.extend(
            goal.givens
                .iter()
                .map(|given| substitute_free_variable(given, variable, &successor)),
        );
        let step_conclusion = substitute_free_variable(&goal.conclusion, variable, &successor);
        Self {
            base: scoped_goal_expression(&base_givens, &base_conclusion),
            step: scoped_goal_expression(&step_givens, &step_conclusion),
        }
    }

    fn matches_base(&self, goal: &Goal) -> bool {
        scoped_goal_expression(&goal.givens, &goal.conclusion) == self.base
    }

    fn matches_step(&self, goal: &Goal) -> bool {
        scoped_goal_expression(&goal.givens, &goal.conclusion) == self.step
    }
}

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

fn substitute_free_variable(
    expression: &Expr<()>,
    variable: &Variable,
    replacement: &Expr<()>,
) -> Expr<()> {
    struct Substitution<'a> {
        variable: &'a Variable,
        replacement: &'a Expr<()>,
    }

    impl VisitMut<()> for Substitution<'_> {
        fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<()>) {
            if matches!(&node.raw, RawExpr::Variable(variable) if variable == self.variable) {
                *node = deep_clone(self.replacement);
            } else {
                visit_mut::visit_expr_mut(self, context, node);
            }
        }

        fn visit_raw_expr_finop_mut(
            &mut self,
            context: VisitContext,
            op: &mut Finop,
            expressions: &mut Vec<Expr<()>>,
        ) {
            for expression in expressions.iter_mut() {
                self.visit_expr_mut(context, expression);
            }
            let mut flattened = Vec::new();
            for expression in expressions.drain(..) {
                if let RawExpr::Finop(nested_op, nested) = &expression.raw
                    && nested_op == op
                {
                    flattened.extend(nested.iter().map(deep_clone));
                } else {
                    flattened.push(expression);
                }
            }
            *expressions = flattened;
        }

        fn visit_raw_expr_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<()>,
        ) {
            self.visit_expr_mut(context, &mut chain.start);
            for (_, expression) in &mut chain.assertions {
                self.visit_expr_mut(context, expression);
            }
        }

        fn visit_raw_expr_seqop_mut(
            &mut self,
            context: VisitContext,
            _op: &mut crate::SeqOp,
            range: &mut crate::Range<()>,
            body: &mut Expr<()>,
        ) {
            self.visit_expr_mut(context, &mut range.from);
            self.visit_expr_mut(context, &mut range.to);
            if range.index_variable != *self.variable {
                self.visit_expr_mut(context, body);
            }
        }
    }

    let mut result = deep_clone(expression);
    Substitution {
        variable,
        replacement,
    }
    .visit_expr_mut(POSITIVE, &mut result);
    result
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
                    ProofContext {
                        tracked,
                        retained: scoped_statements,
                    },
                    run,
                )?;
                if result.validated {
                    if !result.assertions.is_empty() {
                        track_assertions(
                            solver,
                            &result.assertions,
                            step.sentence.clone(),
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
                        symbolic_types,
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
            symbolic_types,
            tracked,
            scoped_statements,
            run,
        );
    }
    validate_claim(
        &goal.conclusion,
        &mut goal.validation,
        solver,
        environment,
        symbolic_types,
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
    let prepared_givens = match ordinary_givens
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

    let extensions = goal_environment_extensions(
        &parent_environment,
        &symbolic_types,
        &environment_givens,
        run.max_dimension,
    )?;
    and_exhaustive(goal, extensions.exhaustive);
    if extensions.environments.is_empty() {
        record_inconsistent_givens(goal, extensions.exhaustive, run.max_dimension);
        return Ok(None);
    }

    let implication = (introduced_variables.is_empty() && !goal.givens.iter().any(is_quantifier))
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
        let mut tracked = parent.tracked.to_vec();
        let mut scoped_statements = parent.scoped_statements.to_vec();
        scoped_statements.extend(retained_givens.iter().cloned());
        for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            tracked.push((tracker, given.clone()));
        }
        if let Some((_, prepared)) = &forced_lower_bound {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            solver.assert(assertion.expression);
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

fn validate_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
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
    tracked: &[(Bool, Expr<()>)],
    run: &mut ValidationRun,
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
    let extensions = expression_environment_extensions(
        &environment,
        symbolic_types,
        &positive,
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
        validated: true,
    })
}

fn validate_quantified_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let spec = match analyze_quantifier(sentence, symbolic_types) {
        Ok(spec) => spec,
        Err(message) => {
            validation
                .checks
                .push(StepCheck::QuantifierInconclusive { message });
            return Ok(ClaimResult::default());
        }
    };
    if !spec.questionable.is_empty() {
        validation.checks.push(StepCheck::QuestionableQuantifier {
            premises: spec.questionable.clone(),
        });
    }
    let inherited_facts = proof_facts(proof.tracked, proof.retained);
    if let Some(fact) = inherited_facts
        .iter()
        .find(|fact| *fact == sentence)
        .cloned()
    {
        validation
            .checks
            .push(StepCheck::EstablishedByFact { fact });
        return Ok(ClaimResult {
            assertions: Vec::new(),
            retained: vec![sentence.clone()],
            validated: true,
        });
    }
    match spec.kind {
        QuantifierKind::Exists => {
            match find_existential_witness(&spec, symbolic_types, &inherited_facts) {
                Some(witness) => {
                    validation.checks.push(StepCheck::ExistentialWitness {
                        assignments: witness.assignments.into_iter().collect(),
                        supporting_facts: witness.supporting_facts,
                    });
                    Ok(ClaimResult {
                        assertions: Vec::new(),
                        retained: vec![sentence.clone()],
                        validated: true,
                    })
                }
                None => {
                    validation.checks.push(StepCheck::QuantifierInconclusive {
                        message: "no common syntactic witness was established".to_owned(),
                    });
                    Ok(ClaimResult::default())
                }
            }
        }
        QuantifierKind::Forall => {
            validate_universal_claim(sentence, spec, validation, solver, environment, proof, run)
        }
    }
}

fn validate_universal_claim(
    sentence: &Expr<()>,
    spec: QuantifierSpec,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let ordinary_premises = spec
        .premises
        .iter()
        .filter(|premise| !is_quantifier(premise))
        .cloned()
        .collect::<Vec<_>>();
    let retained_premises = spec
        .premises
        .iter()
        .filter(|premise| is_quantifier(premise))
        .cloned()
        .collect::<Vec<_>>();
    let prepared_premises = ordinary_premises
        .iter()
        .map(|premise| prepare_expression(&spec.types, premise, POSITIVE))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)?;
    let prepared_body = if is_quantifier(&spec.body) {
        None
    } else {
        Some(
            prepare_expression(&spec.types, &spec.body, POSITIVE)
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)?,
        )
    };
    let extensions = quantifier_environment_extensions(
        &environment,
        &spec.types,
        &prepared_premises,
        prepared_body.as_ref(),
        run.max_dimension,
    )?;
    validation.environments_exhaustive &= extensions.exhaustive;
    let mut feasible = 0;
    let mut all_validated = true;
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut local_tracked = proof.tracked.to_vec();
        let mut local_retained = proof.retained.to_vec();
        local_retained.extend(retained_premises.iter().cloned());
        for (premise, prepared) in ordinary_premises.iter().zip(&prepared_premises) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            local_tracked.push((tracker, premise.clone()));
        }
        match solver.check() {
            SatResult::Sat => {
                feasible += 1;
                if is_quantifier(&spec.body) {
                    let facts = proof_facts(&local_tracked, &local_retained);
                    if let Some(fact) = facts.into_iter().find(|fact| fact == &spec.body) {
                        validation
                            .checks
                            .push(StepCheck::EstablishedByFact { fact });
                    } else {
                        validation.checks.push(StepCheck::QuantifierInconclusive {
                            message: "a nested quantified body requires an exact contextual fact"
                                .to_owned(),
                        });
                        all_validated = false;
                    }
                } else {
                    let result = validate_ordinary_claim(
                        &spec.body,
                        validation,
                        solver,
                        Rc::clone(&extension),
                        &spec.types,
                        &local_tracked,
                        run,
                    )?;
                    all_validated &= result.validated;
                }
            }
            SatResult::Unknown => {
                validation.checks.push(StepCheck::Unknown {
                    environment: Some(Rc::clone(&extension)),
                });
                all_validated = false;
            }
            SatResult::Unsat => {}
        }
        solver.pop(1);
        if !all_validated {
            break;
        }
    }
    if feasible == 0 {
        validation.checks.push(StepCheck::VacuousQuantifier);
        return Ok(ClaimResult::default());
    }
    if all_validated {
        Ok(ClaimResult {
            assertions: Vec::new(),
            retained: vec![sentence.clone()],
            validated: true,
        })
    } else {
        Ok(ClaimResult::default())
    }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum QuantifierKind {
    Forall,
    Exists,
}

struct QuantifierSpec {
    kind: QuantifierKind,
    premises: Vec<Expr<()>>,
    body: Expr<()>,
    introduced: BTreeSet<Variable>,
    questionable: Vec<Expr<()>>,
    types: SymbolicTypeEnvironment,
}

fn quantifier_kind(expression: &Expr<()>) -> Option<QuantifierKind> {
    match expression.raw {
        RawExpr::Finop(Finop::Forall, _) => Some(QuantifierKind::Forall),
        RawExpr::Finop(Finop::Exists, _) => Some(QuantifierKind::Exists),
        _ => None,
    }
}

fn is_quantifier(expression: &Expr<()>) -> bool {
    quantifier_kind(expression).is_some()
}

fn contains_quantifier(expression: &Expr<()>) -> bool {
    #[derive(Default)]
    struct Finder(bool);

    impl Visit<()> for Finder {
        fn visit_raw_expr_finop(&mut self, op: &Finop, expressions: &[Expr<()>]) {
            if matches!(op, Finop::Forall | Finop::Exists) {
                self.0 = true;
            } else {
                crate::visit::visit_raw_expr_finop(self, op, expressions);
            }
        }
    }

    let mut finder = Finder::default();
    finder.visit_expr(expression);
    finder.0
}

fn analyze_quantifier(
    expression: &Expr<()>,
    active_types: &SymbolicTypeEnvironment,
) -> Result<QuantifierSpec, String> {
    let kind = quantifier_kind(expression)
        .ok_or_else(|| "expression is not a supported quantifier".to_owned())?;
    let RawExpr::Finop(_, expressions) = &expression.raw else {
        unreachable!()
    };
    if expressions.len() < 2 {
        return Err("a quantifier requires at least one premise and a body".to_owned());
    }
    let premises = expressions[..expressions.len() - 1].to_vec();
    let body = expressions.last().unwrap().clone();
    let premise_variables = premises
        .iter()
        .map(|premise| free_variables(std::iter::once(premise)))
        .collect::<Vec<_>>();
    let introduced = premise_variables
        .iter()
        .flatten()
        .filter(|variable| !active_types.types.contains_key(*variable))
        .cloned()
        .collect::<BTreeSet<_>>();
    if introduced.is_empty() {
        return Err(
            "a quantifier must introduce at least one fresh variable in its premises".to_owned(),
        );
    }
    let questionable = premises
        .iter()
        .zip(&premise_variables)
        .filter(|(_, variables)| variables.is_disjoint(&introduced))
        .map(|(premise, _)| premise.clone())
        .collect::<Vec<_>>();

    let inferred = infer_symbolic_type_environment(&premises).map_err(|error| error.to_string())?;
    let mut types = active_types.clone();
    for variable in &introduced {
        let ty = inferred.types.get(variable).cloned().ok_or_else(|| {
            format!(
                "missing inferred type for quantified variable {}",
                variable.z3_name()
            )
        })?;
        types.types.insert(variable.clone(), ty);
    }
    if let Some(variable) = free_variables(std::iter::once(&body))
        .into_iter()
        .find(|variable| !types.types.contains_key(variable))
    {
        return Err(format!(
            "quantifier body contains unbound variable {}",
            variable.z3_name()
        ));
    }
    for child in expressions {
        if is_quantifier(child) {
            analyze_quantifier(child, &types)?;
        } else if contains_quantifier(child) {
            return Err("quantifiers embedded beneath another operator are unsupported".to_owned());
        } else {
            prepare_expression(&types, child, POSITIVE).map_err(|error| error.to_string())?;
        }
    }
    Ok(QuantifierSpec {
        kind,
        premises,
        body,
        introduced,
        questionable,
        types,
    })
}

fn proof_facts(tracked: &[(Bool, Expr<()>)], retained: &[Expr<()>]) -> Vec<Expr<()>> {
    tracked
        .iter()
        .map(|(_, expression)| expression.clone())
        .chain(retained.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn quantifier_binders(
    expressions: &[Expr<()>],
    accessible: &BTreeSet<Variable>,
) -> BTreeSet<Variable> {
    let Some((_, premises)) = expressions.split_last() else {
        return BTreeSet::new();
    };
    premises
        .iter()
        .flat_map(|premise| free_variables(std::iter::once(premise)))
        .filter(|variable| !accessible.contains(variable))
        .collect()
}

struct Unifier<'a> {
    metavariables: &'a BTreeSet<Variable>,
    assignments: BTreeMap<Variable, Expr<()>>,
    pattern_accessible: BTreeSet<Variable>,
    candidate_accessible: BTreeSet<Variable>,
    pattern_bound: BTreeSet<Variable>,
    candidate_bound: BTreeSet<Variable>,
}

impl Unifier<'_> {
    fn expression(&mut self, pattern: &Expr<()>, candidate: &Expr<()>) -> bool {
        if let RawExpr::Variable(variable) = &pattern.raw
            && self.metavariables.contains(variable)
            && !self.pattern_bound.contains(variable)
        {
            if !free_variables(std::iter::once(candidate)).is_disjoint(&self.candidate_bound) {
                return false;
            }
            return match self.assignments.get(variable) {
                Some(assigned) => assigned == candidate,
                None => {
                    self.assignments.insert(variable.clone(), candidate.clone());
                    true
                }
            };
        }
        match (&pattern.raw, &candidate.raw) {
            (RawExpr::Hole, RawExpr::Hole) => true,
            (RawExpr::ImplicitDimension(a), RawExpr::ImplicitDimension(b)) => a == b,
            (
                RawExpr::IdentityMatrix { dimension: a },
                RawExpr::IdentityMatrix { dimension: b },
            ) => a == b,
            (
                RawExpr::StandardBasis {
                    index: ai,
                    dimension: ad,
                },
                RawExpr::StandardBasis {
                    index: bi,
                    dimension: bd,
                },
            ) => ad == bd && self.expression(ai, bi),
            (
                RawExpr::ZeroMatrix { rows: ar, cols: ac },
                RawExpr::ZeroMatrix { rows: br, cols: bc },
            ) => ar == br && ac == bc,
            (RawExpr::Type(a), RawExpr::Type(b)) => self.type_expr(a, b),
            (RawExpr::Variable(a), RawExpr::Variable(b)) => a == b,
            (RawExpr::NatLiteral(a), RawExpr::NatLiteral(b)) => a == b,
            (RawExpr::Matrix(a), RawExpr::Matrix(b)) => {
                a.rows == b.rows && a.cols == b.cols && self.expressions(&a.elements, &b.elements)
            }
            (RawExpr::Monop(ao, a), RawExpr::Monop(bo, b)) => ao == bo && self.expression(a, b),
            (RawExpr::Binop(ao, al, ar), RawExpr::Binop(bo, bl, br)) => {
                ao == bo && self.expression(al, bl) && self.expression(ar, br)
            }
            (RawExpr::Triop(ao, aa, ab, ac), RawExpr::Triop(bo, ba, bb, bc)) => {
                ao == bo
                    && self.expression(aa, ba)
                    && self.expression(ab, bb)
                    && self.expression(ac, bc)
            }
            (RawExpr::Finop(ao, a), RawExpr::Finop(bo, b)) if ao == bo => {
                if matches!(ao, Finop::Forall | Finop::Exists) {
                    self.quantified_expressions(a, b)
                } else {
                    self.expressions(a, b)
                }
            }
            (RawExpr::CmpChain(a), RawExpr::CmpChain(b)) => {
                a.assertions.len() == b.assertions.len()
                    && self.expression(&a.start, &b.start)
                    && a.assertions
                        .iter()
                        .zip(&b.assertions)
                        .all(|((ao, ae), (bo, be))| ao == bo && self.expression(ae, be))
            }
            (RawExpr::LogicChain(a), RawExpr::LogicChain(b)) => {
                a.assertions.len() == b.assertions.len()
                    && self.expression(&a.start, &b.start)
                    && a.assertions
                        .iter()
                        .zip(&b.assertions)
                        .all(|((ao, ae), (bo, be))| ao == bo && self.expression(ae, be))
            }
            (RawExpr::Seqop(ao, ar, ab), RawExpr::Seqop(bo, br, bb)) => {
                ao == bo
                    && ar.index_variable == br.index_variable
                    && self.expression(&ar.from, &br.from)
                    && self.expression(&ar.to, &br.to)
                    && self.bound_sequence_body(&ar.index_variable, &br.index_variable, ab, bb)
            }
            _ => false,
        }
    }

    fn expressions(&mut self, pattern: &[Expr<()>], candidate: &[Expr<()>]) -> bool {
        pattern.len() == candidate.len()
            && pattern
                .iter()
                .zip(candidate)
                .all(|(pattern, candidate)| self.expression(pattern, candidate))
    }

    fn quantified_expressions(&mut self, pattern: &[Expr<()>], candidate: &[Expr<()>]) -> bool {
        if pattern.len() != candidate.len() {
            return false;
        }
        let pattern_binders = quantifier_binders(pattern, &self.pattern_accessible);
        let candidate_binders = quantifier_binders(candidate, &self.candidate_accessible);
        let old_pattern_bound = self.pattern_bound.clone();
        let old_candidate_bound = self.candidate_bound.clone();
        let old_pattern_accessible = self.pattern_accessible.clone();
        let old_candidate_accessible = self.candidate_accessible.clone();
        self.pattern_bound.extend(pattern_binders.iter().cloned());
        self.candidate_bound
            .extend(candidate_binders.iter().cloned());
        self.pattern_accessible.extend(pattern_binders);
        self.candidate_accessible.extend(candidate_binders);
        let matched = self.expressions(pattern, candidate);
        self.pattern_bound = old_pattern_bound;
        self.candidate_bound = old_candidate_bound;
        self.pattern_accessible = old_pattern_accessible;
        self.candidate_accessible = old_candidate_accessible;
        matched
    }

    fn bound_sequence_body(
        &mut self,
        pattern_index: &Variable,
        candidate_index: &Variable,
        pattern: &Expr<()>,
        candidate: &Expr<()>,
    ) -> bool {
        let pattern_was_bound = !self.pattern_bound.insert(pattern_index.clone());
        let candidate_was_bound = !self.candidate_bound.insert(candidate_index.clone());
        let matched = self.expression(pattern, candidate);
        if !pattern_was_bound {
            self.pattern_bound.remove(pattern_index);
        }
        if !candidate_was_bound {
            self.candidate_bound.remove(candidate_index);
        }
        matched
    }

    fn type_expr(&mut self, pattern: &TypeExpr<()>, candidate: &TypeExpr<()>) -> bool {
        match (pattern, candidate) {
            (TypeExpr::Bool, TypeExpr::Bool)
            | (TypeExpr::Nat, TypeExpr::Nat)
            | (TypeExpr::Int, TypeExpr::Int)
            | (TypeExpr::Real, TypeExpr::Real) => true,
            (TypeExpr::Matrix(ar, ac), TypeExpr::Matrix(br, bc))
            | (TypeExpr::Seq(ar, ac), TypeExpr::Seq(br, bc)) => {
                self.expression(ar, br) && self.expression(ac, bc)
            }
            _ => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct WitnessMatch {
    assignments: BTreeMap<Variable, Expr<()>>,
    supporting_facts: Vec<Expr<()>>,
}

fn find_existential_witness(
    spec: &QuantifierSpec,
    active_types: &SymbolicTypeEnvironment,
    facts: &[Expr<()>],
) -> Option<WitnessMatch> {
    let requirements = spec.premises.iter().chain(std::iter::once(&spec.body));
    let accessible = active_types.types.keys().cloned().collect::<BTreeSet<_>>();
    let mut matches = BTreeSet::from([WitnessMatch {
        assignments: BTreeMap::new(),
        supporting_facts: Vec::new(),
    }]);
    for requirement in requirements {
        let mut next = BTreeSet::new();
        for state in &matches {
            for fact in facts {
                let mut unifier = Unifier {
                    metavariables: &spec.introduced,
                    assignments: state.assignments.clone(),
                    pattern_accessible: accessible
                        .iter()
                        .chain(spec.introduced.iter())
                        .cloned()
                        .collect(),
                    candidate_accessible: accessible.clone(),
                    pattern_bound: BTreeSet::new(),
                    candidate_bound: BTreeSet::new(),
                };
                if unifier.expression(requirement, fact) {
                    let mut supporting_facts = state.supporting_facts.clone();
                    if !supporting_facts.contains(fact) {
                        supporting_facts.push(fact.clone());
                    }
                    next.insert(WitnessMatch {
                        assignments: unifier.assignments,
                        supporting_facts,
                    });
                }
            }
        }
        matches = next;
        if matches.is_empty() {
            return None;
        }
    }
    matches.into_iter().find(|candidate| {
        spec.introduced
            .iter()
            .all(|v| candidate.assignments.contains_key(v))
    })
}

fn natural_lower_bound(variable: &Variable, start: u64) -> Expr<()> {
    Expr::new(RawExpr::CmpChain(CmpChain {
        start: Expr::new(RawExpr::Variable(variable.clone())),
        assertions: vec![(Cmp::Ge, Expr::new(RawExpr::NatLiteral(start)))],
    }))
}

fn infer_induction_start(
    goal: &Goal,
    variable: &Variable,
    base: &Environment,
    parent_types: &SymbolicTypeEnvironment,
    max_dimension: u64,
) -> Result<Option<u64>, ArgumentValidationError> {
    for value in 0..=max_dimension {
        let replacement = Expr::new(RawExpr::NatLiteral(value));
        let givens = goal
            .givens
            .iter()
            .filter(|given| !is_quantifier(given))
            .map(|given| substitute_free_variable(given, variable, &replacement))
            .collect::<Vec<_>>();
        let conclusion = substitute_free_variable(&goal.conclusion, variable, &replacement);
        let (types, _) = match extend_symbolic_types(parent_types, &givens) {
            Ok(types) => types,
            Err(ArgumentValidationError::Shape(ShapeError::InvalidTyping(_))) => continue,
            Err(error) => return Err(error),
        };
        let prepared_givens = match givens
            .iter()
            .map(|given| prepare_expression(&types, given, POSITIVE))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(prepared) => prepared,
            Err(TypeError::Invalid(_)) => continue,
            Err(error) => return Err(ModelFindingError::from(ToZ3Error::from(error)).into()),
        };
        let prepared_conclusion = match prepare_expression(&types, &conclusion, POSITIVE) {
            Ok(prepared) => prepared,
            Err(TypeError::Invalid(_)) => continue,
            Err(error) => return Err(ModelFindingError::from(ToZ3Error::from(error)).into()),
        };
        let mut assumptions = fixed_assignment_declarations(base, &types)?;
        assumptions.extend(prepared_givens);
        let iterator = match extract_prepared_environment_iterator_with_required_context(
            &types,
            &assumptions,
            std::slice::from_ref(&prepared_conclusion),
            &[],
            max_dimension,
        ) {
            Ok(iterator) => iterator,
            Err(ShapeError::Unsat(_) | ShapeError::InvalidTyping(_)) => continue,
            Err(error) => return Err(error.into()),
        };
        if iterator.into_iter().next().transpose()?.is_some() {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn validate_tactic_fallback(
    goal: &mut Goal,
    solver: &mut Solver,
    base: Rc<Environment>,
    parent_types: &SymbolicTypeEnvironment,
    tracked: &[(Bool, Expr<()>)],
    scoped_statements: &[Expr<()>],
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let ordinary_givens = goal
        .givens
        .iter()
        .filter(|given| !is_quantifier(given))
        .cloned()
        .collect::<Vec<_>>();
    let (mut types, _) = extend_symbolic_types(parent_types, &ordinary_givens)?;
    let Tactic::Induction { variable } = goal.tactic.as_ref().unwrap();
    types.types.insert(variable.clone(), TypeExpr::Nat);
    let prepared_givens = ordinary_givens
        .iter()
        .map(|given| prepare_expression(&types, given, POSITIVE))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)?;
    let extensions =
        goal_environment_extensions(&base, &types, &prepared_givens, run.max_dimension)?;
    goal.validation.environments_exhaustive &= extensions.exhaustive;
    if extensions.environments.is_empty() {
        goal.validation
            .checks
            .push(StepCheck::DimensionallyInvalid {
                environment: base,
                declarations: Vec::new(),
            });
        return Ok(ClaimResult::default());
    }

    let mut all_validated = true;
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut local_tracked = tracked.to_vec();
        for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            local_tracked.push((tracker, given.clone()));
        }
        if matches!(solver.check(), SatResult::Sat) {
            let result = validate_claim(
                &goal.conclusion,
                &mut goal.validation,
                solver,
                Rc::clone(&extension),
                &types,
                ProofContext {
                    tracked: &local_tracked,
                    retained: scoped_statements,
                },
                run,
            )?;
            all_validated &= result.validated;
        }
        solver.pop(1);
    }
    Ok(ClaimResult {
        assertions: Vec::new(),
        retained: Vec::new(),
        validated: all_validated,
    })
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

struct AnalyzedGivens {
    ordinary: Vec<Expr<()>>,
    retained: Vec<Expr<()>>,
    symbolic_types: SymbolicTypeEnvironment,
    introduced: BTreeSet<Variable>,
    questionable: Vec<Expr<()>>,
}

fn analyze_goal_givens(
    parent: &SymbolicTypeEnvironment,
    givens: &[Expr<()>],
    forced_natural: Option<&Variable>,
) -> Result<AnalyzedGivens, String> {
    let mut result = AnalyzedGivens {
        ordinary: Vec::new(),
        retained: Vec::new(),
        symbolic_types: parent.clone(),
        introduced: BTreeSet::new(),
        questionable: Vec::new(),
    };
    let mut forced_inserted = false;
    for given in givens {
        if is_quantifier(given) {
            let spec = analyze_quantifier(given, &result.symbolic_types)?;
            result.questionable.extend(spec.questionable);
            result.retained.push(given.clone());
            continue;
        }
        if let Some(variable) = forced_natural
            && !forced_inserted
        {
            if result.symbolic_types.types.contains_key(variable) {
                return Err(format!(
                    "induction-step binder {} collides with its enclosing scope",
                    variable.z3_name()
                ));
            }
            result
                .symbolic_types
                .types
                .insert(variable.clone(), TypeExpr::Nat);
            result.introduced.insert(variable.clone());
            forced_inserted = true;
        }
        let (types, introduced) =
            extend_symbolic_types(&result.symbolic_types, std::slice::from_ref(given))
                .map_err(|error| error.to_string())?;
        result.symbolic_types = types;
        result.introduced.extend(introduced);
        result.ordinary.push(given.clone());
    }
    if let Some(variable) = forced_natural
        && !forced_inserted
    {
        if result.symbolic_types.types.contains_key(variable) {
            return Err(format!(
                "induction-step binder {} collides with its enclosing scope",
                variable.z3_name()
            ));
        }
        result
            .symbolic_types
            .types
            .insert(variable.clone(), TypeExpr::Nat);
        result.introduced.insert(variable.clone());
    }
    Ok(result)
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

    fn visit_raw_expr_finop(&mut self, op: &Finop, expressions: &[Expr<()>]) {
        if !matches!(op, Finop::Forall | Finop::Exists) {
            crate::visit::visit_raw_expr_finop(self, op, expressions);
            return;
        }
        let Some((body, premises)) = expressions.split_last() else {
            return;
        };
        let mut introduced = BTreeSet::new();
        for premise in premises {
            for variable in free_variables(std::iter::once(premise)) {
                if !self.variables.contains(&variable) && !self.bound.contains(&variable) {
                    introduced.insert(variable);
                }
            }
            self.bound.extend(introduced.iter().cloned());
            self.visit_expr(premise);
        }
        self.visit_expr(body);
        for variable in introduced {
            self.bound.remove(&variable);
        }
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

fn quantifier_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    premises: &[PreparedExpression],
    required_body: Option<&PreparedExpression>,
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let assumptions = declarations
        .iter()
        .chain(premises)
        .cloned()
        .collect::<Vec<_>>();
    let required = required_body.map(std::slice::from_ref).unwrap_or_default();
    let iterator = match extract_prepared_environment_iterator_with_required_context(
        symbolic_types,
        &assumptions,
        required,
        &[],
        max_dimension,
    ) {
        Ok(iterator) => iterator,
        Err(ShapeError::Unsat(_) | ShapeError::InvalidTyping(_)) => {
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
    let (conclusion, tactic) = parse_wts(
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
        tactic,
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

fn parse_wts(node: &Node) -> (Expr<()>, Option<Tactic>) {
    let Node::Paragraph(Paragraph { children, .. }) = node else {
        panic!("WTS must be a paragraph")
    };
    let (label, math, tactic) = match children.as_slice() {
        [Node::Text(label), Node::InlineMath(math)] => (label, math, None),
        [
            Node::Text(label),
            Node::InlineMath(math),
            Node::Text(tactic_label),
            Node::InlineMath(variable),
        ] => {
            assert_eq!(
                tactic_label.value, " by induction on ",
                "unsupported goal tactic"
            );
            let parsed =
                ratex_parser::parse(&variable.value).expect("invalid TeX in induction variable");
            let variable =
                crate::from_tex::expr(&parsed).expect("unsupported TeX in induction variable");
            let RawExpr::Variable(variable) = &variable.raw else {
                panic!("induction target must be a variable")
            };
            (
                label,
                math,
                Some(Tactic::Induction {
                    variable: variable.clone(),
                }),
            )
        }
        _ => panic!("WTS must contain one expression and an optional supported tactic"),
    };
    assert_eq!(label.value, "WTS ", "goal paragraph must start with WTS");
    let parsed = ratex_parser::parse(&math.value).expect("invalid TeX in WTS expression");
    (
        crate::from_tex::expr(&parsed).expect("unsupported TeX in WTS expression"),
        tactic,
    )
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
    let mut wts_children = vec![
        Node::Text(markdown::mdast::Text {
            value: "WTS ".to_owned(),
            position: None,
        }),
        Node::InlineMath(InlineMath {
            value: goal.conclusion.as_latex().to_string(),
            position: None,
        }),
    ];
    if let Some(Tactic::Induction { variable }) = &goal.tactic {
        wts_children.push(Node::Text(markdown::mdast::Text {
            value: " by induction on ".to_owned(),
            position: None,
        }));
        let variable_expression: Expr<()> = Expr::new(RawExpr::Variable(variable.clone()));
        wts_children.push(Node::InlineMath(InlineMath {
            value: variable_expression.as_latex().to_string(),
            position: None,
        }));
    }
    nodes.push(Node::Paragraph(Paragraph {
        children: wts_children,
        position: None,
    }));
    if let Some(details) = validation_details(&goal.conclusion, &goal.validation, expressions) {
        nodes.push(Node::Html(Html {
            value: details,
            position: None,
        }));
    }
    if !goal.steps.is_empty() {
        nodes.push(argument_item_list(&goal.steps, expressions));
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
    if let Some(StepCheck::InvalidTactic { message }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InvalidTactic { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ invalid tactic</summary>\n\n{message}\n</details>"
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
    if let Some(StepCheck::QuantifierInconclusive { message }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Inconclusive</summary>\n\n{message}\n</details>"
        ));
    }
    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::VacuousQuantifier))
    {
        return Some(
            "<details>\n<summary>Inconclusive</summary>\n\nThe quantified premises had no admissible instance in the environments checked.\n</details>"
                .to_owned(),
        );
    }
    if let Some(StepCheck::ExistentialWitness {
        assignments,
        supporting_facts,
    }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    {
        let assignments = assignments
            .iter()
            .map(|(variable, expression)| {
                format!("- ${} = {}$", variable.z3_name(), expression.as_latex())
            })
            .collect::<Vec<_>>()
            .join("\n");
        let warning = validation
            .checks
            .iter()
            .find_map(|check| match check {
                StepCheck::QuestionableQuantifier { premises } => Some(format!(
                    "\n\nThe following premises do not reference a variable introduced by their quantifier:\n\n{}",
                    expression_bullets(premises)
                )),
                _ => None,
            })
            .unwrap_or_default();
        return Some(format!(
            "<details>\n<summary>✅ witness found</summary>\n\nWitness:\n\n{assignments}\n\nMatched facts:\n\n{}{warning}\n</details>",
            expression_bullets(supporting_facts)
        ));
    }
    if let Some(StepCheck::QuestionableQuantifier { premises }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::QuestionableQuantifier { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ questionable quantifier</summary>\n\nThe following premises do not reference a variable introduced by their quantifier:\n\n{}\n</details>",
            expression_bullets(premises)
        ));
    }
    if let Some(StepCheck::IncompleteSubgoals { expected }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::IncompleteSubgoals { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ valid claim, incomplete subgoals</summary>\n\nNo counterexample was found, but the following subgoals were not established:\n\n{}\n</details>",
            expression_bullets(expected)
        ));
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

    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::TacticEstablished))
    {
        if validation.environments_exhaustive {
            return Some(
                "<details>\n<summary>✅ verified</summary>\n\nThe induction base and step were validated.\n</details>"
                    .to_owned(),
            );
        }
        let max_dimension = validation
            .max_dimension
            .unwrap_or_else(|| panic!("validated goal is missing its maximum dimension"));
        return Some(format!(
            "<details>\n<summary>✅ likely</summary>\n\nThe induction base and step were validated up to a maximum dimension of {max_dimension}.\n</details>"
        ));
    }

    let mut present = BTreeSet::new();
    for check in &validation.checks {
        match check {
            StepCheck::Unsat {
                supporting_facts, ..
            } => present.extend(supporting_facts.iter().cloned()),
            StepCheck::EstablishedByFact { fact } => {
                present.insert(fact.clone());
            }
            _ => {}
        }
    }
    let mut seen = BTreeSet::new();
    let supporting_facts: Vec<_> = expressions
        .iter()
        .filter(|expression| present.contains(*expression) && seen.insert((*expression).clone()))
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
    use std::collections::{BTreeMap, BTreeSet};

    use super::{
        Argument, ArgumentItem, Arguments, StepCheck, Tactic, ToFromMd, free_variables,
        infer_induction_start,
    };
    use crate::{Environment, RawExpr, type_resolver::SymbolicTypeEnvironment};

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
    fn induction_tactic_round_trips_and_establishes_a_goal() {
        let input = r#"# Reflexivity by induction

WTS $n = n$ by induction on $n$

1. WTS $0 = 0$
2. Given:

   - $n = n$

   WTS $n + 1 = n + 1$"#;
        let mut argument = Argument::parse_str(input);
        assert_eq!(argument.to_string(), input);
        assert!(matches!(
            argument.root.tactic,
            Some(Tactic::Induction { ref variable }) if variable.name == "n"
        ));

        argument.validate(2).unwrap();
        assert!(
            argument
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::TacticEstablished))
        );
        assert!(!argument.root.validation.environments_exhaustive);
    }

    #[test]
    fn incomplete_induction_falls_back_to_bounded_validation() {
        let mut argument = Argument::parse_str(
            r#"# Incomplete induction

WTS $n = n$ by induction on $n$"#,
        );
        argument.validate(2).unwrap();
        let StepCheck::IncompleteSubgoals { expected } = argument
            .root
            .validation
            .checks
            .iter()
            .find(|check| matches!(check, StepCheck::IncompleteSubgoals { .. }))
            .expect("missing incomplete-subgoals result")
        else {
            unreachable!()
        };
        assert_eq!(expected[0].as_latex().to_string(), "0 = 0");
        assert!(matches!(
            expected[1].raw,
            RawExpr::Finop(crate::Finop::Forall, _)
        ));
        assert_eq!(
            expected[1].as_latex().to_string(),
            r"\forall n = n, n + 1 = n + 1"
        );
        assert!(
            argument
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::Unsat { .. }))
        );
        assert!(
            argument
                .to_string()
                .contains("valid claim, incomplete subgoals")
        );
    }

    #[test]
    fn tactic_bound_natural_appears_in_counterexamples() {
        let mut argument = Argument::parse_str(
            r#"# False induction claim

WTS $n = 0$ by induction on $n$"#,
        );
        argument.validate(2).unwrap();
        let StepCheck::Counterexample { model, .. } = argument
            .root
            .validation
            .checks
            .iter()
            .find(|check| matches!(check, StepCheck::Counterexample { .. }))
            .expect("missing counterexample")
        else {
            unreachable!()
        };
        assert!(model.iter().any(|assignment| {
            assignment.as_latex().to_string() == "n = 1"
                || assignment.as_latex().to_string() == "n = 2"
        }));
    }

    #[test]
    fn induction_binder_is_local_and_may_use_an_arbitrary_name() {
        let mut argument = Argument::parse_str(
            r#"# Local induction binder

WTS $q = q$ by induction on $q$

1. $q = q$
2. WTS $0 = 0$
3. Given:

   - $q = q$

   WTS $q + 1 = q + 1$"#,
        );
        argument.validate(2).unwrap();
        assert!(matches!(
            sentence(&argument, 0).validation.checks[0],
            StepCheck::Error { .. }
        ));
        assert!(
            argument
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::TacticEstablished))
        );
    }

    #[test]
    fn invalid_induction_binders_are_local_goal_errors() {
        let mut collision = Argument::parse_str(
            r#"# Collision

Given:

- $n \in \mathbb{N}$

WTS $n = n$

1. WTS $n = n$ by induction on $n$"#,
        );
        collision.validate(2).unwrap();
        let ArgumentItem::Goal(nested) = &collision.root.steps[0] else {
            panic!("expected nested induction goal")
        };
        assert!(matches!(
            nested.validation.checks[0],
            StepCheck::InvalidTactic { .. }
        ));

        let mut absent = Argument::parse_str(
            r#"# Absent binder

WTS $0 = 0$ by induction on $n$"#,
        );
        absent.validate(2).unwrap();
        assert!(matches!(
            absent.root.validation.checks[0],
            StepCheck::InvalidTactic { .. }
        ));
    }

    #[test]
    fn induction_start_uses_structural_and_given_constraints_not_truth() {
        fn start(markdown: &str, max_dimension: u64) -> Option<u64> {
            let argument = Argument::parse_str(markdown);
            let Some(Tactic::Induction { variable }) = &argument.root.tactic else {
                panic!("expected induction tactic")
            };
            infer_induction_start(
                &argument.root,
                variable,
                &Environment::default(),
                &SymbolicTypeEnvironment::default(),
                max_dimension,
            )
            .unwrap()
        }

        assert_eq!(
            start("# Zero\n\nWTS $n = n$ by induction on $n$", 3),
            Some(0)
        );
        assert_eq!(
            start(
                "# Vector\n\nGiven:\n\n- $x \\in \\mathbb{R}^{n}$\n\nWTS $0 = 1$ by induction on $n$",
                3,
            ),
            Some(1)
        );
        assert_eq!(
            start(
                "# Later\n\nGiven:\n\n- $n \\ge 2$\n\nWTS $n = n$ by induction on $n$",
                4,
            ),
            Some(2)
        );
    }

    #[test]
    fn forall_binds_first_premise_variables_and_warns_about_irrelevant_premises() {
        let quantified = crate::from_tex::expr(
            &ratex_parser::parse(r"\forall x \in \mathbb{R}^{n}, 0 = 0, x = x").unwrap(),
        )
        .unwrap();
        assert!(free_variables(std::iter::once(&quantified)).is_empty());

        let mut argument = Argument::parse_str(
            r#"# Questionable universal

WTS $0 = 0$

1. Given:

   - $\forall x \in \mathbb{R}, 0 = 0, x = x$

   WTS $0 = 0$"#,
        );
        argument.validate(1).unwrap();
        let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
            panic!("expected nested goal")
        };
        assert!(goal.validation.checks.iter().any(|check| matches!(
            check,
            StepCheck::QuestionableQuantifier { premises }
                if premises.iter().any(|premise| premise.as_latex().to_string() == "0 = 0")
        )));
    }

    #[test]
    fn universal_claims_share_step_and_goal_validation() {
        let mut argument = Argument::parse_str(
            r#"# Universal claims

WTS $\forall x \in \mathbb{R}, x x \ge 0$

1. $\forall x \in \mathbb{R}, x x \ge 0$"#,
        );
        argument.validate(1).unwrap();
        assert!(matches!(
            sentence(&argument, 0).validation.checks[0],
            StepCheck::Unsat { .. }
        ));
        assert!(matches!(
            argument.root.validation.checks[0],
            StepCheck::EstablishedByFact { .. }
        ));

        let mut false_claim = Argument::parse_str(
            r#"# False universal

WTS $\forall x \in \mathbb{R}, x x > 0$"#,
        );
        false_claim.validate(1).unwrap();
        let StepCheck::Counterexample { model, .. } = &false_claim.root.validation.checks[0] else {
            panic!("expected a universal counterexample")
        };
        assert!(
            model
                .iter()
                .any(|assignment| assignment.as_latex().to_string() == "x = 0")
        );
    }

    #[test]
    fn universal_naturals_are_bounded_and_empty_domains_are_inconclusive() {
        let mut bounded = Argument::parse_str(
            r#"# Bounded universal

WTS $\forall n \in \mathbb{N}, n = n$"#,
        );
        bounded.validate(2).unwrap();
        assert!(
            bounded
                .root
                .validation
                .checks
                .iter()
                .all(|check| matches!(check, StepCheck::Unsat { .. }))
        );
        assert!(!bounded.root.validation.environments_exhaustive);

        let mut vacuous = Argument::parse_str(
            r#"# Vacuous universal

WTS $\forall n > n, n = n$"#,
        );
        vacuous.validate(2).unwrap();
        assert!(
            vacuous
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::VacuousQuantifier))
        );
    }

    #[test]
    fn universal_vectors_enumerate_local_dimensions() {
        let mut argument = Argument::parse_str(
            r#"# Universal vectors

WTS $\forall x \in \mathbb{R}^{n}, \left\lVert x \right\rVert_{2}^{2} \ge 0$"#,
        );
        argument.validate(2).unwrap();

        assert!(
            argument
                .root
                .validation
                .checks
                .iter()
                .all(|check| matches!(check, StepCheck::Unsat { .. }))
        );
        assert!(!argument.root.validation.environments_exhaustive);
    }

    #[test]
    fn existential_matching_joins_assignments_across_requirements() {
        let quantified =
            crate::from_tex::expr(&ratex_parser::parse(r"\exists x > 0, x < y").unwrap()).unwrap();
        let mut active = SymbolicTypeEnvironment::default();
        active
            .types
            .insert(crate::Variable::new("y"), crate::TypeExpr::Real);
        let spec = super::analyze_quantifier(&quantified, &active).unwrap();
        let facts = [r"1 > 0", r"2 > 0", r"1 < y", r"3 < y"]
            .map(|tex| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap());
        assert!(
            super::find_existential_witness(&spec, &active, &facts).is_some(),
            "direct matching failed for spec {:?} and facts {:?}",
            spec.introduced,
            facts
        );
        let mut witness = Argument::parse_str(
            r#"# Existential witness

Given:

- $y \in \mathbb{R}$
- $1 > 0$
- $2 > 0$
- $1 < y$
- $3 < y$

WTS $\exists x > 0, x < y$"#,
        );
        witness.validate(1).unwrap();
        let StepCheck::ExistentialWitness { assignments, .. } = witness
            .root
            .validation
            .checks
            .iter()
            .find(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
            .expect("missing existential witness")
        else {
            unreachable!()
        };
        assert_eq!(assignments.len(), 1);
        assert_eq!(assignments[0].0.name, "x");
        assert_eq!(assignments[0].1.as_latex().to_string(), "1");

        let mut incompatible = Argument::parse_str(
            r#"# Incompatible witnesses

WTS $\exists x > 0, y > 0, x < y, x > y$

1. $1 > 0$
2. $2 > 0$
3. $1 < 2$
4. $3 > 2$"#,
        );
        incompatible.validate(1).unwrap();
        assert!(
            incompatible
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
        );
    }

    #[test]
    fn retained_quantifiers_support_exact_reuse_and_nested_bodies() {
        let mut argument = Argument::parse_str(
            r#"# Quantified reuse

Given:

- $a \in \mathbb{R}$
- $a = a$

WTS $\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, y = y\right)$

1. $\exists y \in \mathbb{R}, y = y$
2. $\exists y \in \mathbb{R}, y = y$"#,
        );
        argument.validate(1).unwrap();
        assert!(matches!(
            sentence(&argument, 1).validation.checks[0],
            StepCheck::EstablishedByFact { .. }
        ));
        assert!(
            argument
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::EstablishedByFact { .. }))
        );
    }

    #[test]
    fn existential_unification_does_not_leak_inner_binders() {
        let pattern = crate::from_tex::expr(
            &ratex_parser::parse(r"\forall z \in \mathbb{R}, y = z").unwrap(),
        )
        .unwrap();
        let candidate = crate::from_tex::expr(
            &ratex_parser::parse(r"\forall z \in \mathbb{R}, z = z").unwrap(),
        )
        .unwrap();
        let witness_variable = crate::Variable::new("y");
        let mut unifier = super::Unifier {
            metavariables: &BTreeSet::from([witness_variable]),
            assignments: BTreeMap::new(),
            pattern_accessible: BTreeSet::new(),
            candidate_accessible: BTreeSet::new(),
            pattern_bound: BTreeSet::new(),
            candidate_bound: BTreeSet::new(),
        };
        assert!(!unifier.expression(&pattern, &candidate));
    }

    #[test]
    fn existential_goal_uses_direct_children_but_not_internal_descendants() {
        let mut direct = Argument::parse_str(
            r#"# Direct child evidence

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. WTS $1 > 0$
2. WTS $1 < y$"#,
        );
        direct.validate(1).unwrap();
        assert!(
            direct
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
        );

        let mut hidden = Argument::parse_str(
            r#"# Internal evidence stays local

WTS $\exists x > 0, x = x$

1. WTS $0 = 0$

   1. $1 > 0$
   2. $1 = 1$"#,
        );
        hidden.validate(1).unwrap();
        assert!(
            hidden
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
        );
    }

    #[test]
    fn quantified_binders_must_be_fresh_and_introduced_in_premises() {
        let mut shadowed = Argument::parse_str(
            r#"# Shadowed binder

Given:

- $x \in \mathbb{R}$

WTS $\forall x \in \mathbb{R}, x = x$"#,
        );
        shadowed.validate(1).unwrap();
        assert!(
            shadowed
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
        );

        let mut body_only = Argument::parse_str(
            r#"# Body-only variable

WTS $\exists 0 = 0, x = x$"#,
        );
        body_only.validate(1).unwrap();
        assert!(
            body_only
                .root
                .validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
        );
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
    #[should_panic(expected = "goal body must be an ordered list")]
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
