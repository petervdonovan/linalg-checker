use std::{
    error::Error,
    fmt::{self, Display},
};

use markdown::{
    Constructs, ParseOptions,
    mdast::{Heading, InlineMath, List, ListItem, Node, Paragraph, Root, Text},
};
use z3::{
    Model as Z3Model, SatResult, Solver,
    ast::{Algebraic, Bool, Dynamic, Real},
};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Matrix, Model, Monop, NaturalParameter, RawExpr,
    TypeExpr, Variable,
    enumerable_envspec::{
        ShapeError, extract_prepared_environment_iterator_with_required_context,
        infer_symbolic_type_environment,
    },
    preprocessing::{PreparedExpression, prepare_expression},
    to_z3::{LoweredExistence, LoweredSideCondition, ToZ3Error, Z3Object, to_z3},
    type_resolver::{MaybeTyped, SymbolicTypeEnvironment},
    visit_mut::VisitContext,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelFindingError {
    Lowering(ToZ3Error),
    Shape(ShapeError),
    NonBooleanAssertion,
    MissingModel,
    UnsupportedModel(&'static str),
    ModelValueOutOfRange(&'static str),
}

impl Display for ModelFindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lowering(error) => error.fmt(f),
            Self::Shape(error) => error.fmt(f),
            Self::NonBooleanAssertion => f.write_str("test-case assertion must be Boolean"),
            Self::MissingModel => f.write_str("Z3 returned sat without providing a model"),
            Self::UnsupportedModel(message) | Self::ModelValueOutOfRange(message) => {
                f.write_str(message)
            }
        }
    }
}

impl Error for ModelFindingError {}

impl From<ToZ3Error> for ModelFindingError {
    fn from(error: ToZ3Error) -> Self {
        Self::Lowering(error)
    }
}

impl From<ShapeError> for ModelFindingError {
    fn from(error: ShapeError) -> Self {
        Self::Shape(error)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TestCase<Conclusion> {
    pub name: String,
    pub sentences: Vec<Expr<()>>,
    pub environment: Vec<Expr<()>>,
    pub conclusion: Conclusion,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TestCases<Conclusion>(pub Vec<TestCase<Conclusion>>);

#[derive(Debug, PartialEq, Eq)]
pub struct NotSolvedYet;

#[derive(Debug, PartialEq, Eq)]
pub enum ModelOrUnsat {
    Unsat,
    UnsatUpToDimension(u64),
    Unknown,
    Model(Model, Vec<ExistenceWarning>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExistenceWarning {
    MayBeUndefined {
        introduced_variable: Variable,
        witness: Model,
    },
    Assumed {
        introduced_variable: Variable,
    },
}

pub trait ToFromMd {
    fn parse_str(s: &str) -> Self
    where
        Self: Sized,
    {
        let options = ParseOptions {
            constructs: Constructs {
                math_text: true,
                math_flow: true,
                ..Constructs::default()
            },
            ..ParseOptions::default()
        };
        Self::parse_md(&markdown::to_mdast(s, &options).unwrap())
    }

    fn parse_md(md: &Node) -> Self;
    fn to_md(&self) -> Node;
}

macro_rules! impl_display {
    ($Tfm:ty) => {
        impl Display for $Tfm {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&render_md(&self.to_md()))
            }
        }
    };
}
impl_display!(TestCase<NotSolvedYet>);
impl_display!(ModelOrUnsat);
impl_display!(TestCase<ModelOrUnsat>);
impl_display!(TestCases<NotSolvedYet>);
impl_display!(TestCases<ModelOrUnsat>);

impl<Conclusion: ToFromMd> ToFromMd for TestCase<Conclusion> {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        assert!(
            matches!(
                children.first(),
                Some(Node::Heading(Heading { depth: 1, .. }))
            ),
            "test case must start with a level-one heading"
        );
        let name = heading_text(&children[0]);
        let environment_start = section_start(children, "Environment");
        let sentences_start = section_start(children, "Sentences");
        let conclusion_start = section_start(children, "Conclusion");
        assert!(
            environment_start < sentences_start && sentences_start < conclusion_start,
            "test case sections are out of order"
        );

        let mut environment = parse_expression_section(
            &children[environment_start + 1..sentences_start],
            "environment",
        );
        validate_environment_entries(&environment);
        environment.sort();
        let sentences = parse_expression_section(
            &children[sentences_start + 1..conclusion_start],
            "sentences",
        );
        let conclusion = Conclusion::parse_md(&Node::Root(Root {
            children: children[conclusion_start + 1..].to_vec(),
            position: None,
        }));

        Self {
            name,
            sentences,
            environment,
            conclusion,
        }
    }

    fn to_md(&self) -> Node {
        let mut children = vec![heading(1, &self.name), heading(2, "Environment")];
        if !self.environment.is_empty() {
            let mut environment = self.environment.clone();
            environment.sort();
            children.push(expression_list(&environment));
        }
        children.push(heading(2, "Sentences"));
        if !self.sentences.is_empty() {
            children.push(expression_list(&self.sentences));
        }
        children.push(heading(2, "Conclusion"));
        children.extend(root_children(&self.conclusion.to_md()).iter().cloned());
        Node::Root(Root {
            children,
            position: None,
        })
    }
}

impl<Conclusion: ToFromMd> ToFromMd for TestCases<Conclusion> {
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
        assert!(!starts.is_empty(), "test-case collection is empty");

        let cases = starts
            .iter()
            .enumerate()
            .map(|(index, start)| {
                let end = starts.get(index + 1).copied().unwrap_or(children.len());
                TestCase::parse_md(&Node::Root(Root {
                    children: children[*start..end].to_vec(),
                    position: None,
                }))
            })
            .collect();
        Self(cases)
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "test-case collection is empty");
        Node::Root(Root {
            children: self
                .0
                .iter()
                .flat_map(|case| root_children(&case.to_md()).to_vec())
                .collect(),
            position: None,
        })
    }
}

impl TestCases<NotSolvedYet> {
    pub fn find_models(self) -> Result<TestCases<ModelOrUnsat>, ModelFindingError> {
        Ok(TestCases(
            self.0
                .into_iter()
                .map(|test_case| {
                    let TestCase {
                        name,
                        sentences,
                        environment,
                        conclusion: NotSolvedYet,
                    } = test_case;
                    let conclusion = solve_given_environment(&environment, &sentences)?;
                    Ok(TestCase {
                        name,
                        sentences,
                        environment,
                        conclusion,
                    })
                })
                .collect::<Result<_, ModelFindingError>>()?,
        ))
    }
}

pub(crate) fn solve_given_environment(
    declarations: &[Expr<()>],
    assertions: &[Expr<()>],
) -> Result<ModelOrUnsat, ModelFindingError> {
    let symbolic_types = infer_symbolic_type_environment(declarations)?;
    let context = VisitContext {
        logical_polarity: true,
        active_ranges: Vec::new(),
    };
    let prepared = declarations
        .iter()
        .chain(assertions)
        .map(|expression| prepare_expression(&symbolic_types, expression, context.clone()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ToZ3Error::from)?;
    let environment = assignment_from_declarations(declarations)?;
    solve_prepared_environment(&environment, &symbolic_types, &prepared)
}

pub(crate) fn solve_prepared_environment(
    environment: &Environment,
    variable_types: &SymbolicTypeEnvironment,
    assertions: &[PreparedExpression],
) -> Result<ModelOrUnsat, ModelFindingError> {
    let solver = Solver::new();
    let mut lowered_assertions = Vec::new();
    assert_natural_assignment(&solver, environment);
    for assertion in assertions {
        let lowered = lower_prepared_boolean(environment, assertion)?;
        assert_definitions(&solver, &lowered.side_conditions)?;
        solver.assert(lowered.expression.clone());
        lowered_assertions.push(lowered);
    }
    match solver.check() {
        SatResult::Unsat => Ok(ModelOrUnsat::Unsat),
        SatResult::Unknown => Ok(ModelOrUnsat::Unknown),
        SatResult::Sat => Ok(ModelOrUnsat::Model(
            extract_model(
                environment,
                variable_types,
                &solver.get_model().ok_or(ModelFindingError::MissingModel)?,
            )?,
            existence_warnings(environment, variable_types, &lowered_assertions)?,
        )),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CounterexampleSearch {
    Found,
    NotFound,
    Unknown,
}

pub(crate) struct CounterexampleProgram {
    symbolic_types: SymbolicTypeEnvironment,
    prepared_program: Vec<PreparedExpression>,
    max_dimension: u64,
}

impl CounterexampleProgram {
    pub(crate) fn new(program: &[Expr<()>], max_dimension: u64) -> Result<Self, ModelFindingError> {
        let symbolic_types = infer_symbolic_type_environment(program)?;
        let positive = VisitContext::positive();
        let prepared_program = program
            .iter()
            .map(|expression| prepare_expression(&symbolic_types, expression, positive.clone()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(ToZ3Error::from)?;
        Ok(Self {
            symbolic_types,
            prepared_program,
            max_dimension,
        })
    }

    pub(crate) fn environments(
        &self,
    ) -> Result<crate::enumerable_envspec::EnvironmentIterator, ModelFindingError> {
        extract_prepared_environment_iterator_with_required_context(
            &self.symbolic_types,
            &self.prepared_program,
            &[],
            &[],
            self.max_dimension,
        )
        .map_err(ModelFindingError::from)
    }

    pub(crate) fn checker<'a>(
        &'a self,
        environment: &'a Environment,
    ) -> Result<FixedEnvironmentCounterexampleChecker<'a>, ModelFindingError> {
        let solver = Solver::new();
        assert_natural_assignment(&solver, environment);
        for assertion in &self.prepared_program {
            if !matches!(assertion.expression.meta.get_type(), Ok(TypeExpr::Bool)) {
                continue;
            }
            let assertion = lower_prepared_boolean(environment, assertion)?;
            assert_definitions(&solver, &assertion.side_conditions)?;
            solver.assert(assertion.expression);
        }
        Ok(FixedEnvironmentCounterexampleChecker {
            solver,
            environment,
            symbolic_types: &self.symbolic_types,
        })
    }
}

pub(crate) struct FixedEnvironmentCounterexampleChecker<'a> {
    solver: Solver,
    environment: &'a Environment,
    symbolic_types: &'a SymbolicTypeEnvironment,
}

impl FixedEnvironmentCounterexampleChecker<'_> {
    pub(crate) fn check(
        &mut self,
        claims: &[Expr<()>],
    ) -> Result<CounterexampleSearch, ModelFindingError> {
        let negative = VisitContext::negative();
        let prepared_claims = claims
            .iter()
            .map(|expression| prepare_expression(self.symbolic_types, expression, negative.clone()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(ToZ3Error::from)?;
        let lowered_claims = prepared_claims
            .iter()
            .map(|claim| lower_prepared_boolean(self.environment, claim))
            .collect::<Result<Vec<_>, _>>()?;
        self.solver.push();
        for claim in &lowered_claims {
            assert_definitions(&self.solver, &claim.side_conditions)?;
        }
        let expressions = lowered_claims
            .iter()
            .map(|claim| claim.expression.clone())
            .collect::<Vec<_>>();
        self.solver.assert(Bool::and(&expressions).not());
        let result = match self.solver.check() {
            SatResult::Sat => CounterexampleSearch::Found,
            SatResult::Unknown => CounterexampleSearch::Unknown,
            SatResult::Unsat => CounterexampleSearch::NotFound,
        };
        self.solver.pop(1);
        Ok(result)
    }
}

fn assignment_from_declarations(
    declarations: &[Expr<()>],
) -> Result<Environment, ModelFindingError> {
    let mut environment = Environment::default();
    for declaration in declarations {
        let RawExpr::CmpChain(CmpChain { start, assertions }) = &declaration.raw else {
            continue;
        };
        let [(Cmp::Eq, right)] = assertions.as_slice() else {
            continue;
        };
        let (RawExpr::Variable(variable), RawExpr::NatLiteral(value)) = (&start.raw, &right.raw)
        else {
            continue;
        };
        let previous = environment
            .natural_assignment
            .insert(NaturalParameter::Variable(variable.clone()), *value);
        if previous.is_some_and(|previous| previous != *value) {
            return Err(ModelFindingError::Shape(ShapeError::Unsat(
                "given environment contains conflicting natural assignments".to_owned(),
            )));
        }
    }
    Ok(environment)
}

#[derive(Clone)]
pub(crate) struct LoweredBoolean {
    pub expression: z3::ast::Bool,
    pub side_conditions: Vec<LoweredSideCondition>,
}

pub(crate) fn existence_warnings(
    environment: &Environment,
    variable_types: &SymbolicTypeEnvironment,
    assertions: &[LoweredBoolean],
) -> Result<Vec<ExistenceWarning>, ModelFindingError> {
    let mut conditions = std::collections::BTreeMap::new();
    for assertion in assertions {
        for condition in &assertion.side_conditions {
            conditions
                .entry(condition.introduced_variable.clone())
                .or_insert_with(|| condition.clone());
        }
    }
    let mut warnings = Vec::new();
    for condition in conditions.values() {
        match &condition.existence {
            LoweredExistence::Guaranteed => {}
            LoweredExistence::Assumed => warnings.push(ExistenceWarning::Assumed {
                introduced_variable: Variable::new(condition.display_name.clone()),
            }),
            LoweredExistence::Checkable(warning_assertions) => {
                let solver = Solver::new();
                assert_natural_assignment(&solver, environment);
                for assertion in assertions {
                    solver.assert(assertion.expression.clone());
                    for other in &assertion.side_conditions {
                        if other.introduced_variable != condition.introduced_variable {
                            assert_definitions(&solver, std::slice::from_ref(other))?;
                        }
                    }
                }
                for warning in warning_assertions {
                    solver.assert(z3_boolean(warning)?);
                }
                match solver.check() {
                    SatResult::Unsat => {}
                    SatResult::Unknown => warnings.push(ExistenceWarning::Assumed {
                        introduced_variable: Variable::new(condition.display_name.clone()),
                    }),
                    SatResult::Sat => warnings.push(ExistenceWarning::MayBeUndefined {
                        introduced_variable: Variable::new(condition.display_name.clone()),
                        witness: extract_model(
                            environment,
                            variable_types,
                            &solver.get_model().ok_or(ModelFindingError::MissingModel)?,
                        )?,
                    }),
                }
            }
        }
    }
    Ok(warnings)
}

pub(crate) fn lower_prepared_boolean(
    environment: &Environment,
    assertion: &PreparedExpression,
) -> Result<LoweredBoolean, ModelFindingError> {
    let lowered = to_z3(environment, assertion)?;
    let Z3Object::Z3(assertion) = lowered.expression else {
        return Err(ModelFindingError::NonBooleanAssertion);
    };
    Ok(LoweredBoolean {
        expression: assertion
            .as_bool()
            .ok_or(ModelFindingError::NonBooleanAssertion)?,
        side_conditions: lowered.side_conditions,
    })
}

pub(crate) fn assert_definitions(
    solver: &Solver,
    side_conditions: &[LoweredSideCondition],
) -> Result<(), ModelFindingError> {
    for condition in side_conditions {
        for assertion in &condition.defining_assertions {
            solver.assert(z3_boolean(assertion)?);
        }
    }
    Ok(())
}

pub(crate) fn z3_boolean(value: &Z3Object) -> Result<z3::ast::Bool, ModelFindingError> {
    let Z3Object::Z3(value) = value else {
        return Err(ModelFindingError::NonBooleanAssertion);
    };
    value
        .as_bool()
        .ok_or(ModelFindingError::NonBooleanAssertion)
}

pub(crate) fn assert_natural_assignment(solver: &Solver, environment: &Environment) {
    let mut assignment = environment.natural_assignment.iter().collect::<Vec<_>>();
    assignment.sort_by_key(|(parameter, _)| *parameter);
    for (parameter, value) in assignment {
        solver.assert(
            z3::ast::Int::new_const(parameter.z3_name()).eq(z3::ast::Int::from_u64(*value)),
        );
    }
}

pub(crate) fn extract_model(
    environment: &Environment,
    variable_types: &SymbolicTypeEnvironment,
    model: &Z3Model,
) -> Result<Model, ModelFindingError> {
    let mut variables: Vec<_> = variable_types.types.iter().collect();
    variables.sort_by_key(|(variable, _)| *variable);
    variables
        .into_iter()
        .map(|(variable, ty)| extract_variable(environment, variable_types, model, variable, ty))
        .collect::<Result<Vec<_>, _>>()
        .map(|assignments| assignments.into_iter().flatten().collect())
}

fn extract_variable(
    environment: &Environment,
    variable_types: &SymbolicTypeEnvironment,
    model: &Z3Model,
    variable: &crate::Variable,
    ty: &TypeExpr<()>,
) -> Result<Vec<Expr<()>>, ModelFindingError> {
    match ty {
        TypeExpr::Seq(element, length) => {
            let RawExpr::Type(element) = &element.raw else {
                return Err(ModelFindingError::UnsupportedModel(
                    "sequence element must be a type expression",
                ));
            };
            if matches!(element, TypeExpr::Seq(_, _)) {
                return Err(ModelFindingError::UnsupportedModel(
                    "nested sequence extraction is not supported",
                ));
            }
            let length = environment
                .evaluate_natural(length)
                .map_err(ToZ3Error::from)?;
            let sequence: Expr<()> = Expr::new(RawExpr::Variable(variable.clone()));
            let prepared = prepare_expression(
                variable_types,
                &sequence,
                VisitContext {
                    logical_polarity: true,
                    active_ranges: Vec::new(),
                },
            )
            .map_err(ToZ3Error::from)?;
            let Z3Object::Sequence(values) = to_z3(environment, &prepared)?.expression else {
                return Err(ModelFindingError::UnsupportedModel(
                    "sequence variable did not lower to a sequence value",
                ));
            };
            if values.len() != usize::try_from(length).map_err(|_| ToZ3Error::DimensionOverflow)? {
                return Err(ModelFindingError::UnsupportedModel(
                    "lowered sequence length does not match its symbolic type",
                ));
            }
            values
                .into_iter()
                .enumerate()
                .map(|(position, value)| {
                    let index =
                        u64::try_from(position).map_err(|_| ToZ3Error::DimensionOverflow)? + 1;
                    let left = Expr::new(RawExpr::Binop(
                        Binop::SingleSubscript,
                        Expr::new(RawExpr::Variable(variable.clone())),
                        Expr::new(RawExpr::NatLiteral(index)),
                    ));
                    let right = z3_object_model_value(model, value)?;
                    Ok(model_equality(left, right))
                })
                .collect()
        }
        TypeExpr::Bool => Err(ModelFindingError::UnsupportedModel(
            "Boolean model extraction is not supported",
        )),
        _ => {
            let left = Expr::new(RawExpr::Variable(variable.clone()));
            let right = z3_object_model_value(
                model,
                to_z3(
                    environment,
                    &prepare_expression(
                        variable_types,
                        &left,
                        VisitContext {
                            logical_polarity: true,
                            active_ranges: Vec::new(),
                        },
                    )
                    .map_err(ToZ3Error::from)?,
                )?
                .expression,
            )?;
            Ok(vec![model_equality(left, right)])
        }
    }
}

fn z3_object_model_value(model: &Z3Model, value: Z3Object) -> Result<Expr<()>, ModelFindingError> {
    match value {
        Z3Object::Z3(value) => scalar_model_value(model, value),
        Z3Object::Matrix(matrix) => Ok(Expr::new(RawExpr::Matrix(Matrix {
            rows: matrix.rows,
            cols: matrix.cols,
            elements: matrix
                .elements
                .into_iter()
                .map(|value| match value {
                    Z3Object::Z3(value) => scalar_model_value(model, value),
                    Z3Object::Matrix(_) => Err(ModelFindingError::UnsupportedModel(
                        "nested matrices are not supported in Z3 models",
                    )),
                    Z3Object::Sequence(_) => Err(ModelFindingError::UnsupportedModel(
                        "sequences nested in matrices are not supported in Z3 models",
                    )),
                })
                .collect::<Result<_, _>>()?,
        }))),
        Z3Object::Sequence(_) => Err(ModelFindingError::UnsupportedModel(
            "nested sequence extraction is not supported",
        )),
    }
}

fn model_equality(left: Expr<()>, right: Expr<()>) -> Expr<()> {
    Expr::new(RawExpr::CmpChain(CmpChain {
        start: left,
        assertions: vec![(Cmp::Eq, right)],
    }))
}

fn scalar_model_value(model: &Z3Model, value: Dynamic) -> Result<Expr<()>, ModelFindingError> {
    if let Some(value) = value.as_int() {
        let Some(value) = model.get_const_interp(&value) else {
            return Ok(Expr::new(RawExpr::Hole));
        };
        if let Some(value) = value.as_i64() {
            Ok(signed_integer(value))
        } else if let Some(value) = value.as_u64() {
            Ok(Expr::new(RawExpr::NatLiteral(value)))
        } else {
            Err(ModelFindingError::ModelValueOutOfRange(
                "integer model value does not fit in the supported literal range",
            ))
        }
    } else if let Some(value) = value.as_real() {
        let Some(value) = model.get_const_interp(&value) else {
            return Ok(Expr::new(RawExpr::Hole));
        };
        if let Some((numerator, denominator)) = value.as_rational() {
            rational_expression(numerator, denominator)
        } else {
            square_root_expression(value)
        }
    } else {
        Err(ModelFindingError::UnsupportedModel(
            "model extraction requires an integer or real scalar",
        ))
    }
}

fn square_root_expression(value: Real) -> Result<Expr<()>, ModelFindingError> {
    let algebraic = Algebraic::try_from(value).map_err(|_| {
        ModelFindingError::UnsupportedModel("real model value is not a concrete algebraic number")
    })?;
    let squared: Real = algebraic.power(2).into();
    let (numerator, denominator) =
        squared
            .as_rational()
            .ok_or(ModelFindingError::UnsupportedModel(
                "algebraic model value is not a square root of a supported rational",
            ))?;
    let root = Expr::new(RawExpr::Binop(
        Binop::Power,
        rational_expression(numerator, denominator)?,
        Expr::new(RawExpr::Binop(
            Binop::Div,
            Expr::new(RawExpr::NatLiteral(1)),
            Expr::new(RawExpr::NatLiteral(2)),
        )),
    ));
    if algebraic.is_negative() {
        Ok(Expr::new(RawExpr::Monop(Monop::Neg, root)))
    } else {
        Ok(root)
    }
}

fn rational_expression(numerator: i64, denominator: i64) -> Result<Expr<()>, ModelFindingError> {
    if denominator <= 0 {
        return Err(ModelFindingError::ModelValueOutOfRange(
            "Z3 returned a rational with a nonpositive denominator",
        ));
    }
    let numerator = signed_integer(numerator);
    if denominator == 1 {
        Ok(numerator)
    } else {
        Ok(Expr::new(RawExpr::Binop(
            Binop::Div,
            numerator,
            Expr::new(RawExpr::NatLiteral(denominator.try_into().map_err(
                |_| {
                    ModelFindingError::ModelValueOutOfRange(
                        "rational denominator does not fit in u64",
                    )
                },
            )?)),
        )))
    }
}

fn signed_integer(value: i64) -> Expr<()> {
    let magnitude = Expr::new(RawExpr::NatLiteral(value.unsigned_abs()));
    if value < 0 {
        Expr::new(RawExpr::Monop(Monop::Neg, magnitude))
    } else {
        magnitude
    }
}

impl ToFromMd for NotSolvedYet {
    fn parse_md(md: &Node) -> Self {
        assert_eq!(
            paragraph_text(single_root_child(md)),
            "Not solved yet",
            "expected an unsolved conclusion"
        );
        NotSolvedYet
    }

    fn to_md(&self) -> Node {
        root(vec![paragraph_text_node("Not solved yet")])
    }
}

impl ToFromMd for ModelOrUnsat {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        match children {
            [node] if paragraph_text(node) == "Unsat" => Self::Unsat,
            [node]
                if paragraph_text(node)
                    .strip_prefix("Unsat up to dimension ")
                    .is_some() =>
            {
                let dimension = paragraph_text(node)
                    .strip_prefix("Unsat up to dimension ")
                    .unwrap()
                    .parse()
                    .expect("bounded unsat dimension must be a natural-number literal");
                Self::UnsatUpToDimension(dimension)
            }
            [node] if paragraph_text(node) == "Unknown" => Self::Unknown,
            [label, list] if paragraph_text(label) == "Model" => {
                Self::Model(parse_expression_list(list), Vec::new())
            }
            [
                label,
                list,
                Node::Heading(Heading { depth: 3, .. }),
                warnings @ ..,
            ] if paragraph_text(label) == "Model" => Self::Model(
                parse_expression_list(list),
                parse_existence_warnings(warnings),
            ),
            _ => panic!(
                "conclusion must be Unsat, bounded Unsat, Unknown, or Model followed by an expression list"
            ),
        }
    }

    fn to_md(&self) -> Node {
        match self {
            Self::Unsat => root(vec![paragraph_text_node("Unsat")]),
            Self::UnsatUpToDimension(dimension) => root(vec![paragraph_text_node(&format!(
                "Unsat up to dimension {dimension}"
            ))]),
            Self::Unknown => root(vec![paragraph_text_node("Unknown")]),
            Self::Model(model, warnings) => {
                assert!(
                    !model.is_empty(),
                    "model must contain at least one expression"
                );
                let mut children = vec![paragraph_text_node("Model"), expression_list(model)];
                if !warnings.is_empty() {
                    children.push(heading(3, "Warnings"));
                    children.extend(render_existence_warnings(warnings));
                }
                root(children)
            }
        }
    }
}

fn render_existence_warnings(warnings: &[ExistenceWarning]) -> Vec<Node> {
    let mut nodes = Vec::new();
    for warning in warnings {
        match warning {
            ExistenceWarning::MayBeUndefined {
                introduced_variable,
                witness,
            } => {
                nodes.push(warning_paragraph(
                    "The expression ",
                    introduced_variable,
                    " may be undefined. For example:",
                ));
                nodes.push(expression_list(witness));
            }
            ExistenceWarning::Assumed {
                introduced_variable,
            } => nodes.push(warning_paragraph(
                "The existence of ",
                introduced_variable,
                " was assumed without checking.",
            )),
        }
    }
    nodes
}

fn warning_paragraph(prefix: &str, variable: &Variable, suffix: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![
            text(prefix),
            Node::InlineMath(InlineMath {
                value: variable.name.clone(),
                position: None,
            }),
            text(suffix),
        ],
        position: None,
    })
}

fn parse_existence_warnings(nodes: &[Node]) -> Vec<ExistenceWarning> {
    let mut warnings = Vec::new();
    let mut index = 0;
    while index < nodes.len() {
        let Node::Paragraph(Paragraph { children, .. }) = &nodes[index] else {
            panic!("existence warning must start with a paragraph")
        };
        let [
            Node::Text(Text { value: prefix, .. }),
            Node::InlineMath(InlineMath { value, .. }),
            Node::Text(Text { value: suffix, .. }),
        ] = children.as_slice()
        else {
            panic!("existence warning has an invalid format")
        };
        let introduced_variable = Variable::new(value.clone());
        if prefix == "The expression " && suffix == " may be undefined. For example:" {
            let witness = parse_expression_list(
                nodes
                    .get(index + 1)
                    .unwrap_or_else(|| panic!("undefinedness warning is missing its witness")),
            );
            warnings.push(ExistenceWarning::MayBeUndefined {
                introduced_variable,
                witness,
            });
            index += 2;
        } else if prefix == "The existence of " && suffix == " was assumed without checking." {
            warnings.push(ExistenceWarning::Assumed {
                introduced_variable,
            });
            index += 1;
        } else {
            panic!("existence warning has unrecognized text")
        }
    }
    warnings
}

pub(crate) fn parse_expression_section(nodes: &[Node], name: &str) -> Vec<Expr<()>> {
    if nodes.is_empty() {
        Vec::new()
    } else {
        assert_eq!(nodes.len(), 1, "{name} must contain one expression list");
        parse_expression_list(&nodes[0])
    }
}

fn validate_environment_entries(expressions: &[Expr<()>]) {
    for expression in expressions {
        match &expression.raw {
            RawExpr::Binop(Binop::ElementOf, left, right) => {
                assert!(
                    matches!(left.raw, RawExpr::Variable(_)),
                    "environment membership must have a variable on the left"
                );
                assert!(
                    matches!(right.raw, RawExpr::Type(_)),
                    "environment membership must have a type on the right"
                );
            }
            RawExpr::CmpChain(CmpChain { assertions, .. })
                if matches!(
                    assertions.as_slice(),
                    [(Cmp::Eq, right)] if matches!(right.raw, RawExpr::NatLiteral(_))
                ) => {}
            _ => panic!("expression does not have a valid environment-entry format"),
        }
    }
}

fn parse_expression_list(node: &Node) -> Vec<Expr<()>> {
    let Node::List(List {
        children,
        ordered: false,
        ..
    }) = node
    else {
        panic!("expected an unordered list of expressions")
    };
    children.iter().map(parse_expression_item).collect()
}

pub(crate) fn parse_expression_item(node: &Node) -> Expr<()> {
    let Node::ListItem(ListItem { children, .. }) = node else {
        panic!("expression list contains a non-list-item node")
    };
    let [Node::Paragraph(Paragraph { children, .. })] = children.as_slice() else {
        panic!("expression list item must contain one paragraph")
    };
    let [Node::InlineMath(InlineMath { value, .. })] = children.as_slice() else {
        panic!("expression list item must contain exactly one inline math expression")
    };
    let parsed = ratex_parser::parse(value).expect("invalid TeX in Markdown expression");
    crate::from_tex::expr(&parsed).expect("unsupported TeX in Markdown expression")
}

pub(crate) fn expression_list(expressions: &[Expr<()>]) -> Node {
    Node::List(List {
        children: expressions
            .iter()
            .map(|expression| {
                Node::ListItem(ListItem {
                    children: vec![Node::Paragraph(Paragraph {
                        children: vec![Node::InlineMath(InlineMath {
                            value: expression.as_latex().to_string(),
                            position: None,
                        })],
                        position: None,
                    })],
                    position: None,
                    spread: false,
                    checked: None,
                })
            })
            .collect(),
        position: None,
        ordered: false,
        start: None,
        spread: false,
    })
}

pub(crate) fn root(children: Vec<Node>) -> Node {
    Node::Root(Root {
        children,
        position: None,
    })
}

pub(crate) fn root_children(node: &Node) -> &[Node] {
    let Node::Root(Root { children, .. }) = node else {
        panic!("expected a Markdown root")
    };
    children
}

fn single_root_child(node: &Node) -> &Node {
    let [child] = root_children(node) else {
        panic!("expected exactly one Markdown block")
    };
    child
}

pub(crate) fn heading(depth: u8, value: &str) -> Node {
    Node::Heading(Heading {
        children: vec![text(value)],
        position: None,
        depth,
    })
}

pub(crate) fn heading_text(node: &Node) -> String {
    let Node::Heading(Heading { children, .. }) = node else {
        panic!("expected a heading")
    };
    inline_text(children)
}

pub(crate) fn section_start(nodes: &[Node], name: &str) -> usize {
    nodes
        .iter()
        .position(|node| {
            matches!(node, Node::Heading(Heading { depth: 2, .. })) && heading_text(node) == name
        })
        .unwrap_or_else(|| panic!("missing {name} section"))
}

fn paragraph_text_node(value: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![text(value)],
        position: None,
    })
}

fn paragraph_text(node: &Node) -> String {
    let Node::Paragraph(Paragraph { children, .. }) = node else {
        panic!("expected a paragraph")
    };
    inline_text(children)
}

fn inline_text(nodes: &[Node]) -> String {
    nodes
        .iter()
        .map(|node| match node {
            Node::Text(Text { value, .. }) => value.as_str(),
            _ => panic!("expected plain text"),
        })
        .collect()
}

fn text(value: &str) -> Node {
    Node::Text(Text {
        value: value.to_owned(),
        position: None,
    })
}

pub(crate) fn render_md(node: &Node) -> String {
    fn block(node: &Node) -> String {
        match node {
            Node::Heading(Heading {
                children, depth, ..
            }) => format!("{} {}", "#".repeat((*depth).into()), inline(children)),
            Node::Paragraph(Paragraph { children, .. }) => inline(children),
            Node::List(List {
                children,
                ordered: false,
                ..
            }) => children
                .iter()
                .map(|item| {
                    let Node::ListItem(ListItem { children, .. }) = item else {
                        panic!("list contains a non-list-item node")
                    };
                    let [Node::Paragraph(Paragraph { children, .. })] = children.as_slice() else {
                        panic!("list item must contain one paragraph")
                    };
                    format!("- {}", inline(children))
                })
                .collect::<Vec<_>>()
                .join("\n"),
            Node::List(List {
                children,
                ordered: true,
                start,
                ..
            }) => {
                let start = start.unwrap_or(1);
                children
                    .iter()
                    .enumerate()
                    .map(|(offset, item)| {
                        let Node::ListItem(ListItem { children, .. }) = item else {
                            panic!("list contains a non-list-item node")
                        };
                        let mut blocks = children.iter().map(block);
                        let first = blocks
                            .next()
                            .unwrap_or_else(|| panic!("ordered list item is empty"));
                        let number = start + u32::try_from(offset).unwrap();
                        let mut rendered = format!("{number}. {first}");
                        for child in blocks {
                            let child = child
                                .lines()
                                .map(|line| {
                                    if line.is_empty() {
                                        String::new()
                                    } else {
                                        format!("   {line}")
                                    }
                                })
                                .collect::<Vec<_>>()
                                .join("\n");
                            rendered.push_str("\n\n");
                            rendered.push_str(&child);
                        }
                        rendered
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            }
            Node::Html(html) => html.value.clone(),
            _ => panic!("unsupported Markdown block in canonical renderer"),
        }
    }

    fn inline(nodes: &[Node]) -> String {
        nodes
            .iter()
            .map(|node| match node {
                Node::Text(Text { value, .. }) => value.clone(),
                Node::InlineMath(InlineMath { value, .. }) => format!("${value}$"),
                _ => panic!("unsupported inline Markdown in canonical renderer"),
            })
            .collect()
    }

    root_children(node)
        .iter()
        .map(block)
        .collect::<Vec<_>>()
        .join("\n\n")
}

#[cfg(test)]
mod tests {
    use std::fmt::{Debug, Display};

    use expect_test::expect;
    use ratex_parser::parse;
    use z3::{
        SatResult, Solver,
        ast::{Int, Real},
    };

    use super::{
        ModelFindingError, ModelOrUnsat, NotSolvedYet, TestCase, TestCases, ToFromMd,
        extract_model, solve_given_environment,
    };
    use crate::{
        Binop, Cmp, CmpChain, Environment, Expr, RawExpr, TypeExpr, Variable,
        type_resolver::SymbolicTypeEnvironment,
    };

    fn variable(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    fn equality(name: &str, value: u64) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: variable(name),
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(value)))],
        }))
    }

    fn symbolic_types(
        entries: impl IntoIterator<Item = (Variable, TypeExpr<()>)>,
    ) -> SymbolicTypeEnvironment {
        SymbolicTypeEnvironment {
            types: entries.into_iter().collect(),
        }
    }

    fn declaration(variable: Variable, ty: TypeExpr<()>) -> Expr<()> {
        Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(variable)),
            Expr::new(RawExpr::Type(ty)),
        ))
    }

    fn matrix_type(rows: u64, cols: u64) -> TypeExpr<()> {
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows)),
            Expr::new(RawExpr::NatLiteral(cols)),
        )
    }

    fn sequence_type(element: TypeExpr<()>, length: u64) -> TypeExpr<()> {
        TypeExpr::Seq(
            Expr::new(RawExpr::Type(element)),
            Expr::new(RawExpr::NatLiteral(length)),
        )
    }

    fn assert_stable<T>(input: &str) -> String
    where
        T: ToFromMd + Display + PartialEq + Debug,
    {
        let parsed = T::parse_str(input);
        let rendered = parsed.to_string();
        let reparsed = T::parse_str(&rendered);
        assert_eq!(parsed, reparsed);
        assert_eq!(rendered, reparsed.to_string());
        rendered
    }

    #[test]
    fn unsolved_case_round_trips_with_canonical_environment_order() {
        let input = r#"# Types

## Environment

- $k = 3$
- $x \in \mathbb{R}$
- $A \in \mathbb{R}^{2 \times 3}$
- $b \in \mathbb{B}$
- $n \in \mathbb{N}$
- $z \in \mathbb{Z}$

## Sentences

- $A \in \mathbb{R}^{2 \times 3}$
- $n = k$

## Conclusion

Not solved yet"#;

        expect![[r#"
            # Types

            ## Environment

            - $A \in \mathbb{R}^{2 \times 3}$
            - $b \in \mathbb{B}$
            - $n \in \mathbb{N}$
            - $x \in \mathbb{R}$
            - $z \in \mathbb{Z}$
            - $k = 3$

            ## Sentences

            - $A \in \mathbb{R}^{2 \times 3}$
            - $n = k$

            ## Conclusion

            Not solved yet"#]]
        .assert_eq(&assert_stable::<TestCase<NotSolvedYet>>(input));
    }

    #[test]
    fn model_and_unsat_cases_round_trip() {
        let unsat = r#"# Contradiction

## Environment

## Sentences

- $x = 1$

## Conclusion

Unsat"#;
        let model = r#"# Example

## Environment

- $x \in \mathbb{R}$

## Sentences

- $x = 2$

## Conclusion

Model

- $x = 2$
- $y = 3$"#;

        assert_eq!(assert_stable::<TestCase<ModelOrUnsat>>(unsat), unsat);
        assert_eq!(assert_stable::<TestCase<ModelOrUnsat>>(model), model);
    }

    #[test]
    fn unknown_conclusion_round_trips() {
        let unknown = r#"# Incomplete

## Environment

## Sentences

## Conclusion

Unknown"#;

        assert_eq!(assert_stable::<TestCase<ModelOrUnsat>>(unknown), unknown);
    }

    #[test]
    fn collections_of_both_conclusion_families_round_trip() {
        let unsolved = r#"# First

## Environment

## Sentences

## Conclusion

Not solved yet

# Second

## Environment

- $n \in \mathbb{N}$

## Sentences

## Conclusion

Not solved yet"#;
        let solved = r#"# Unsat

## Environment

## Sentences

## Conclusion

Unsat

# Model

## Environment

## Sentences

## Conclusion

Model

- $x = 1$"#;

        assert_eq!(assert_stable::<TestCases<NotSolvedYet>>(unsolved), unsolved);
        assert_eq!(assert_stable::<TestCases<ModelOrUnsat>>(solved), solved);
    }

    #[test]
    fn programmatic_environment_rendering_is_deterministic() {
        let environment = vec![
            declaration(Variable::new("x"), TypeExpr::Real),
            declaration(Variable::new("A"), matrix_type(2, 3)),
            declaration(Variable::new("b"), TypeExpr::Bool),
            equality("k", 3),
        ];
        let case = TestCase {
            name: "Order".to_owned(),
            sentences: vec![equality("x", 1)],
            environment,
            conclusion: ModelOrUnsat::Unsat,
        };

        expect![[r#"
            # Order

            ## Environment

            - $A \in \mathbb{R}^{2 \times 3}$
            - $b \in \mathbb{B}$
            - $x \in \mathbb{R}$
            - $k = 3$

            ## Sentences

            - $x = 1$

            ## Conclusion

            Unsat"#]]
        .assert_eq(&case.to_string());
    }

    fn malformed_environment(entry: &str) {
        TestCase::<NotSolvedYet>::parse_str(&format!(
            "# Bad\n\n## Environment\n\n- ${entry}$\n\n## Sentences\n\n## Conclusion\n\nNot solved yet"
        ));
    }

    #[test]
    #[should_panic(expected = "environment membership must have a variable on the left")]
    fn environment_rejects_nonvariable_membership_subject() {
        malformed_environment(r"1 \in \mathbb{R}");
    }

    #[test]
    #[should_panic(expected = "environment membership must have a type on the right")]
    fn environment_rejects_nontype_membership_object() {
        malformed_environment(r"x \in A");
    }

    #[test]
    #[should_panic(expected = "environment membership must have a variable on the left")]
    fn environment_rejects_reversed_membership() {
        malformed_environment(r"\mathbb{R} \in x");
    }

    #[test]
    fn one_by_one_matrix_environment_type_remains_a_matrix() {
        let case = TestCase {
            name: "Canonical".to_owned(),
            sentences: Vec::new(),
            environment: vec![declaration(Variable::new("A"), matrix_type(1, 1))],
            conclusion: NotSolvedYet,
        };
        let parsed = TestCase::<NotSolvedYet>::parse_str(&case.to_string());
        assert_eq!(
            parsed.environment,
            vec![declaration(Variable::new("A"), matrix_type(1, 1))]
        );
    }

    #[test]
    fn model_extraction_rejects_booleans() {
        let boolean = Variable::new("b");
        let error = TestCases(vec![TestCase {
            name: "Boolean".to_owned(),
            sentences: vec![Expr::new(RawExpr::Variable(boolean.clone()))],
            environment: vec![declaration(boolean, TypeExpr::Bool)],
            conclusion: NotSolvedYet,
        }])
        .find_models()
        .unwrap_err();
        assert_eq!(
            error.to_string(),
            "Boolean model extraction is not supported"
        );
    }

    #[test]
    fn solver_rejects_non_boolean_assertions() {
        let error = solve_given_environment(&[], &[Expr::new(RawExpr::NatLiteral(1))]).unwrap_err();
        assert_eq!(error, ModelFindingError::NonBooleanAssertion);
    }

    #[test]
    fn unconstrained_scalar_is_extracted_as_a_hole() {
        let solver = Solver::new();
        assert_eq!(solver.check(), SatResult::Sat);
        let environment = Environment::default();
        let types = symbolic_types([(Variable::new("x"), TypeExpr::Real)]);
        let extracted = extract_model(&environment, &types, &solver.get_model().unwrap()).unwrap();
        let RawExpr::CmpChain(equality) = &extracted[0].raw else {
            panic!("expected an equality")
        };
        assert!(matches!(equality.assertions[0].1.raw, RawExpr::Hole));
    }

    #[test]
    fn square_root_model_values_are_extracted_as_half_powers() {
        fn real_rational(numerator: i64, denominator: i64) -> Real {
            Real::from_int(&Int::from_i64(numerator)) / Real::from_int(&Int::from_i64(denominator))
        }

        for (numerator, denominator, positive, expected) in [
            (2, 1, true, r"2^{\frac{1}{2}}"),
            (2, 1, false, r"-2^{\frac{1}{2}}"),
            (1, 2, true, r"\left(\frac{1}{2}\right)^{\frac{1}{2}}"),
        ] {
            let x = Real::new_const("x");
            let solver = Solver::new();
            solver.assert((&x * &x).eq(real_rational(numerator, denominator)));
            if positive {
                solver.assert(x.gt(real_rational(0, 1)));
            } else {
                solver.assert(x.lt(real_rational(0, 1)));
            }
            assert_eq!(solver.check(), SatResult::Sat);

            let environment = Environment::default();
            let types = symbolic_types([(Variable::new("x"), TypeExpr::Real)]);
            let extracted =
                extract_model(&environment, &types, &solver.get_model().unwrap()).unwrap();
            let RawExpr::CmpChain(equality) = &extracted[0].raw else {
                panic!("expected an equality")
            };
            let value = &equality.assertions[0].1;
            assert_eq!(value.as_latex().to_string(), expected);
            assert_eq!(
                crate::from_tex::expr(&parse(expected).unwrap()).unwrap(),
                *value
            );
        }
    }

    #[test]
    fn other_algebraic_model_values_remain_unsupported() {
        let x = Real::new_const("x");
        let solver = Solver::new();
        solver.assert((&x * &x * &x).eq(Real::from_int(&Int::from_i64(2))));
        solver.assert(x.gt(Real::from_int(&Int::from_i64(0))));
        assert_eq!(solver.check(), SatResult::Sat);

        let environment = Environment::default();
        let types = symbolic_types([(Variable::new("x"), TypeExpr::Real)]);
        assert_eq!(
            extract_model(&environment, &types, &solver.get_model().unwrap()).unwrap_err(),
            ModelFindingError::UnsupportedModel(
                "algebraic model value is not a square root of a supported rational"
            )
        );
    }

    #[test]
    fn matrix_extraction_preserves_constrained_and_unconstrained_cells() {
        let solver = Solver::new();
        solver.assert(Real::new_const("A_{1,1}").eq(Real::from_int(&Int::from_u64(1))));
        assert_eq!(solver.check(), SatResult::Sat);
        let environment = Environment::default();
        let types = symbolic_types([(Variable::new("A"), matrix_type(1, 2))]);
        let extracted = extract_model(&environment, &types, &solver.get_model().unwrap()).unwrap();
        let RawExpr::CmpChain(equality) = &extracted[0].raw else {
            panic!("expected an equality")
        };
        let RawExpr::Matrix(matrix) = &equality.assertions[0].1.raw else {
            panic!("expected a matrix value")
        };
        assert!(matches!(matrix.elements[0].raw, RawExpr::NatLiteral(1)));
        assert!(matches!(matrix.elements[1].raw, RawExpr::Hole));
    }

    #[test]
    fn sequence_extraction_emits_indexed_equalities() {
        let solver = Solver::new();
        solver.assert(Real::new_const("z_{1}").eq(Real::from_int(&Int::from_u64(2))));
        assert_eq!(solver.check(), SatResult::Sat);
        let environment = Environment::default();
        let types = symbolic_types([(Variable::new("z"), sequence_type(TypeExpr::Real, 2))]);
        let extracted = extract_model(&environment, &types, &solver.get_model().unwrap()).unwrap();
        assert_eq!(extracted.len(), 2);
        for (index, equality) in extracted.iter().enumerate() {
            let RawExpr::CmpChain(equality) = &equality.raw else {
                panic!("expected an equality")
            };
            assert!(matches!(
                equality.start.raw,
                RawExpr::Binop(Binop::SingleSubscript, _, ref subscript)
                    if matches!(subscript.raw, RawExpr::NatLiteral(value) if value == index as u64 + 1)
            ));
        }
        let RawExpr::CmpChain(first) = &extracted[0].raw else {
            unreachable!()
        };
        let RawExpr::CmpChain(second) = &extracted[1].raw else {
            unreachable!()
        };
        assert!(matches!(first.assertions[0].1.raw, RawExpr::NatLiteral(2)));
        assert!(matches!(second.assertions[0].1.raw, RawExpr::Hole));
    }
}
