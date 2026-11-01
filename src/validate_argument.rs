use crate::timing::Timings;
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
    NaturalDeduction {
        proof: crate::natural_deduction::NaturalDeductionProof,
        supporting_facts: Vec<Expr<()>>,
    },
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

impl Goal {
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
    pub fn validate(
        &mut self,
        max_dimension: u64,
        timings: &Timings,
    ) -> Result<(), ArgumentValidationError> {
        let _total = timings.scope("total_ms");
        let before = timings.scope("before_preprocessing_complete_ms");
        self.error = None;
        self.root.reset(max_dimension);
        let mut context = crate::natural_deduction::ProofContext::default();
        let mut run = ValidationRun {
            timings: timings.clone(),
            max_dimension,
            next_tracker: 0,
            givens: Vec::new(),
            lexical_expressions: Vec::new(),
            interpretations: BTreeMap::new(),
        };
        drop(before);
        let _after = timings.scope("after_preprocessing_complete_ms");
        natural_deduction::validate_goal(&mut self.root, &mut context, &mut run, None)?;
        Ok(())
    }
}

impl Arguments {
    /// The supplied collector controls whether this collection is timed.
    /// Returned collectors are independent records, one per argument.
    pub fn validate(&mut self, max_dimension: u64, timings: &Timings) -> Vec<Timings> {
        let mut records = Vec::with_capacity(self.0.len());
        for argument in &mut self.0 {
            let record = if timings.enabled() {
                Timings::new(&argument.name, max_dimension)
            } else {
                let mut record = Timings::default();
                record.test_case = argument.name.clone();
                record.max_dimension = max_dimension;
                record
            };
            if let Err(error) = argument.validate(max_dimension, &record) {
                argument.error = Some(error);
            }
            records.push(record);
        }
        records
    }
}

#[derive(Default)]
struct ClaimResult {
    validated: bool,
}
struct ValidationRun {
    timings: Timings,
    givens: Vec<PreparedExpression>,
    lexical_expressions: Vec<Expr<()>>,
    interpretations: BTreeMap<crate::natural_deduction::FactId, PreparedExpression>,
    max_dimension: u64,
    next_tracker: usize,
}
#[derive(Clone)]
struct TrackedFact {
    tracker: Bool,
    sentence: Expr<()>,
}
mod induction;
use induction::{InductionObligations, infer_induction_start, natural_lower_bound};
fn scoped_goal_expression(givens: &[Expr<()>], conclusion: &Expr<()>) -> Expr<()> {
    if givens.is_empty() {
        return deep_clone(conclusion);
    }
    let mut expressions = givens.iter().map(deep_clone).collect::<Vec<_>>();
    expressions.push(deep_clone(conclusion));
    Expr::new(RawExpr::Finop(Finop::Forall, expressions))
}
fn exported_goal_expression(
    introduced: &BTreeSet<Variable>,
    givens: &[Expr<()>],
    conclusion: &Expr<()>,
) -> Expr<()> {
    if introduced.is_empty() {
        scoped_statement_expression(givens, conclusion)
    } else {
        scoped_goal_expression(givens, conclusion)
    }
}
fn fresh_tracker(next: &mut usize) -> Bool {
    let tracker = Bool::new_const(format!("argument_fact_{}", *next));
    *next += 1;
    tracker
}
fn track_assertions(
    solver: &mut Solver,
    assertions: &[crate::model_finding::LoweredBoolean],
    sentence: Expr<()>,
    tracked: &mut Vec<TrackedFact>,
    next: &mut usize,
) -> Result<(), ModelFindingError> {
    let mut expressions = Vec::new();
    for assertion in assertions {
        assert_definitions(solver, &assertion.side_conditions)?;
        expressions.push(assertion.expression.clone());
    }
    let tracker = fresh_tracker(next);
    solver.assert_and_track(Bool::and(&expressions), &tracker);
    tracked.push(TrackedFact { tracker, sentence });
    Ok(())
}
fn record_inconsistent_givens(goal: &mut Goal, exhaustive: bool, max_dimension: u64) {
    goal.validation.checks.push(StepCheck::InconsistentGivens {
        max_dimension: (!exhaustive).then_some(max_dimension),
    });
}

#[allow(clippy::too_many_arguments)]
fn validate_ordinary_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    tracked: &[TrackedFact],
    run: &mut ValidationRun,
    require_positive: bool,
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
        &run.timings,
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
        &run.timings,
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
    let contextual_forms = if require_positive {
        vec![positive.clone(), negative.clone()]
    } else {
        vec![negative.clone()]
    };
    let extensions = expression_environment_extensions(
        &environment,
        symbolic_types,
        &contextual_forms,
        run.max_dimension,
        &run.timings,
    )?;
    validation.environments_exhaustive &= extensions.exhaustive;
    if extensions.environments.is_empty() {
        validation.checks.push(StepCheck::DimensionallyInvalid {
            environment: Rc::clone(&environment),
            declarations: concrete_declarations(symbolic_types, &environment)?,
        });
        return Ok(ClaimResult::default());
    }

    for extension in extensions.environments {
        let extension = Rc::new(extension);
        let _environment_time = run.timings.environment(&extension, symbolic_types);
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
        match run.timings.check(solver, "z3_real_ms") {
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
                if require_positive {
                    solver.push();
                    assert_natural_assignment(solver, &extension);
                    let positive = lower_prepared_boolean(&extension, &positive)?;
                    let warnings = check_step_existence(
                        solver,
                        Rc::clone(&extension),
                        symbolic_types,
                        &positive.side_conditions,
                        &run.timings,
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
                } else {
                    validation.checks.push(StepCheck::Unsat {
                        environment: extension,
                        supporting_facts,
                    });
                }
            }
        }
    }
    Ok(ClaimResult { validated: true })
}

mod natural_deduction;

mod quantifier;
use crate::type_resolver::{QuantifierKind, QuantifierSpec, analyze_quantifier};

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
    check_step_existence, concrete_declarations, core_facts, ensure_expression_bound,
    expression_environment_extensions, extend_symbolic_types, fixed_assignment_declarations,
    goal_environment_extensions,
};

mod markdown;
#[cfg(test)]
mod tests;
