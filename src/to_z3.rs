use std::{
    error::Error,
    fmt::{self, Display},
    ops::{Add, Div, Mul, Neg},
};

use z3::ast::{Bool, Int, Real};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Logic, LogicChain, Matrix, Monop,
    NaturalEvaluationError, RawExpr, Type, TypeExpr, Variable,
    elaboration::{ElaborationError, elaborate},
    preprocessing::PreparedExpression,
    type_resolver::{MaybeTyped, TypeError},
    visit_mut::Existence,
    z3_utils::compare_int,
};

#[derive(Clone)]
pub enum Z3Object {
    Matrix(Matrix<Z3Object>),
    Z3(z3::ast::Dynamic),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToZ3Error {
    Elaboration(ElaborationError),
    Type(TypeError),
    Natural(NaturalEvaluationError),
    Unsupported(&'static str),
    InvalidOperands(&'static str),
    Shape(&'static str),
    Empty(&'static str),
    DimensionOverflow,
    InvalidMatrixLiteral,
}

impl Display for ToZ3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elaboration(error) => error.fmt(f),
            Self::Type(error) => error.fmt(f),
            Self::Natural(error) => error.fmt(f),
            Self::Unsupported(message)
            | Self::InvalidOperands(message)
            | Self::Shape(message)
            | Self::Empty(message) => f.write_str(message),
            Self::DimensionOverflow => f.write_str("matrix dimensions overflow usize"),
            Self::InvalidMatrixLiteral => {
                f.write_str("matrix element count does not match its dimensions")
            }
        }
    }
}

impl Error for ToZ3Error {}

impl From<TypeError> for ToZ3Error {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<ElaborationError> for ToZ3Error {
    fn from(error: ElaborationError) -> Self {
        Self::Elaboration(error)
    }
}

impl From<NaturalEvaluationError> for ToZ3Error {
    fn from(error: NaturalEvaluationError) -> Self {
        Self::Natural(error)
    }
}

#[derive(Clone)]
pub struct ToZ3Result {
    pub expression: Z3Object,
    pub side_conditions: Vec<LoweredSideCondition>,
}

#[derive(Clone)]
pub struct LoweredSideCondition {
    pub introduced_variable: Variable,
    pub display_name: String,
    pub introduced_type: Type,
    pub defining_assertions: Vec<Z3Object>,
    pub existence: LoweredExistence,
}

#[derive(Clone)]
pub enum LoweredExistence {
    Guaranteed,
    Checkable(Vec<Z3Object>),
    Assumed,
}

impl Neg for Z3Object {
    type Output = Result<Self, ToZ3Error>;

    fn neg(self) -> Self::Output {
        match self {
            Self::Z3(expression) => {
                if let Some(expression) = expression.as_int() {
                    Ok(Self::Z3((-expression).into()))
                } else if let Some(expression) = expression.as_real() {
                    Ok(Self::Z3((-expression).into()))
                } else {
                    Err(ToZ3Error::InvalidOperands(
                        "negation requires a numeric scalar",
                    ))
                }
            }
            Self::Matrix(_) => Err(ToZ3Error::InvalidOperands(
                "matrix negation must be elaborated before Z3 lowering",
            )),
        }
    }
}

impl Add for Z3Object {
    type Output = Result<Self, ToZ3Error>;

    fn add(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Ok(Self::Z3((left + right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Ok(Self::Z3((left + right).into()))
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Ok(Self::Z3((Real::from_int(&left) + right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Ok(Self::Z3((left + Real::from_int(&right)).into()))
                } else {
                    Err(ToZ3Error::InvalidOperands(
                        "addition requires numeric scalars",
                    ))
                }
            }
            (Self::Matrix(_), _) | (_, Self::Matrix(_)) => Err(ToZ3Error::InvalidOperands(
                "matrix addition must be elaborated before Z3 lowering",
            )),
        }
    }
}

impl Mul for Z3Object {
    type Output = Result<Self, ToZ3Error>;

    fn mul(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Ok(Self::Z3((left * right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Ok(Self::Z3((left * right).into()))
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Ok(Self::Z3((Real::from_int(&left) * right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Ok(Self::Z3((left * Real::from_int(&right)).into()))
                } else {
                    Err(ToZ3Error::InvalidOperands(
                        "multiplication requires numeric scalars",
                    ))
                }
            }
            (Self::Matrix(_), _) | (_, Self::Matrix(_)) => Err(ToZ3Error::InvalidOperands(
                "matrix multiplication must be elaborated before Z3 lowering",
            )),
        }
    }
}

impl Div for Z3Object {
    type Output = Result<Self, ToZ3Error>;

    fn div(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Ok(Self::Z3((left / right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Ok(Self::Z3((left / right).into()))
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Ok(Self::Z3((Real::from_int(&left) / right).into()))
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Ok(Self::Z3((left / Real::from_int(&right)).into()))
                } else {
                    Err(ToZ3Error::InvalidOperands(
                        "division requires numeric scalars",
                    ))
                }
            }
            (Self::Matrix(_), _) | (_, Self::Matrix(_)) => Err(ToZ3Error::InvalidOperands(
                "matrix division must be elaborated before Z3 lowering",
            )),
        }
    }
}

fn compare(left: Z3Object, comparison: Cmp, right: Z3Object) -> Result<Bool, ToZ3Error> {
    match (left, right) {
        (Z3Object::Z3(left), Z3Object::Z3(right)) => {
            if left.as_bool().is_some() || right.as_bool().is_some() {
                Err(ToZ3Error::InvalidOperands(
                    "boolean scalars cannot be compared",
                ))
            } else if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                Ok(compare_int(&left, comparison, &right))
            } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                Ok(compare_real(left, comparison, right))
            } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                Ok(compare_real(Real::from_int(&left), comparison, right))
            } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                Ok(compare_real(left, comparison, Real::from_int(&right)))
            } else {
                Err(ToZ3Error::InvalidOperands(
                    "comparison requires numeric scalars",
                ))
            }
        }
        (Z3Object::Matrix(_), _) | (_, Z3Object::Matrix(_)) => Err(ToZ3Error::InvalidOperands(
            "matrix comparison must be elaborated before Z3 lowering",
        )),
    }
}

fn compare_real(left: Real, comparison: Cmp, right: Real) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Ne => left.eq(right).not(),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
    }
}

/// Lowers an expression that has already passed through the ordered symbolic
/// preprocessing pipeline.
///
/// The context stored in `prepared` describes the caller's intended logical
/// use. A negatively prepared Boolean is still returned without negation; the
/// counterexample caller remains responsible for applying `not()`.
pub fn to_z3(
    environment: &Environment,
    prepared: &PreparedExpression,
) -> Result<ToZ3Result, ToZ3Error> {
    let elaborated = elaborate(environment, prepared)?;
    let expression = &elaborated.expression;
    let side_conditions = &elaborated.side_conditions;

    let expression = lower(environment, expression)?;
    let side_conditions = side_conditions
        .iter()
        .map(|condition| {
            Ok(LoweredSideCondition {
                introduced_variable: condition.introduced_variable.clone(),
                display_name: condition.display_name.clone(),
                introduced_type: condition.introduced_type.clone(),
                defining_assertions: condition
                    .defining_assertions
                    .iter()
                    .map(|assertion| lower(environment, assertion))
                    .collect::<Result<_, _>>()?,
                existence: match &condition.existence {
                    Existence::Guaranteed => LoweredExistence::Guaranteed,
                    Existence::Checkable(assertions) => LoweredExistence::Checkable(
                        assertions
                            .iter()
                            .map(|assertion| lower(environment, assertion))
                            .collect::<Result<_, _>>()?,
                    ),
                    Existence::Assumed => LoweredExistence::Assumed,
                },
            })
        })
        .collect::<Result<_, ToZ3Error>>()?;
    Ok(ToZ3Result {
        expression,
        side_conditions,
    })
}

fn lower<Metadata: MaybeTyped + Clone>(
    γ: &Environment,
    e: &Expr<Metadata>,
) -> Result<Z3Object, ToZ3Error> {
    match &e.raw {
        RawExpr::Hole
        | RawExpr::ImplicitDimension(_)
        | RawExpr::IdentityMatrix { .. }
        | RawExpr::StandardBasis { .. }
        | RawExpr::ZeroMatrix { .. }
        | RawExpr::Type(_)
        | RawExpr::Seqop(_, _, _)
        | RawExpr::Triop(_, _, _, _) => Err(ToZ3Error::Unsupported(
            "expression was not removed by concrete elaboration",
        )),
        RawExpr::Variable(variable) => {
            let ty = e.meta.get_type()?.concretize(γ)?;
            match ty {
                Type::Bool | Type::Nat | Type::Int | Type::Real => {
                    lower_typed_name(variable.z3_name(), &ty)
                }
                Type::Matrix(_, _) | Type::Seq(_) => Err(ToZ3Error::Unsupported(
                    "nonscalar variable remains after concrete elaboration",
                )),
            }
        }
        RawExpr::NatLiteral(value) => Ok(Z3Object::Z3(match e.meta.get_type()? {
            TypeExpr::Real => Real::from_int(&Int::from_u64(*value)).into(),
            TypeExpr::Nat | TypeExpr::Int => Int::from_u64(*value).into(),
            _ => {
                return Err(ToZ3Error::InvalidOperands(
                    "numeric literal has a nonnumeric scalar type",
                ));
            }
        })),
        RawExpr::Monop(Monop::Neg, inner) => lower(γ, inner)?.neg(),
        RawExpr::Binop(Binop::Div, left, right) => lower(γ, left)? / lower(γ, right)?,
        RawExpr::Finop(Finop::Plus, expressions) => {
            lower_finite(γ, expressions, Add::add, "addition")
        }
        RawExpr::Finop(Finop::Times, expressions) => {
            lower_finite(γ, expressions, Mul::mul, "multiplication")
        }
        RawExpr::Finop(Finop::And, expressions) => lower_boolean_finite(γ, expressions, Finop::And),
        RawExpr::Finop(Finop::Or, expressions) => lower_boolean_finite(γ, expressions, Finop::Or),
        RawExpr::Matrix(matrix) => lower_flat_matrix(γ, matrix),
        RawExpr::CmpChain(chain) => lower_cmp_chain(γ, chain),
        RawExpr::LogicChain(chain) => lower_logic_chain(γ, chain),
        RawExpr::Monop(_, _) | RawExpr::Binop(_, _, _) | RawExpr::Finop(_, _) => Err(
            ToZ3Error::Unsupported("expression is not supported by to_z3"),
        ),
    }
}

fn lower_flat_matrix<Metadata: MaybeTyped + Clone>(
    environment: &Environment,
    matrix: &Matrix<Expr<Metadata>>,
) -> Result<Z3Object, ToZ3Error> {
    let expected = matrix
        .rows
        .checked_mul(matrix.cols)
        .ok_or(ToZ3Error::DimensionOverflow)?;
    if matrix.elements.len() != expected || (matrix.rows == 0) != (matrix.cols == 0) {
        return Err(ToZ3Error::InvalidMatrixLiteral);
    }
    let elements = matrix
        .elements
        .iter()
        .map(|cell| {
            let Z3Object::Z3(cell) = lower(environment, cell)? else {
                return Err(ToZ3Error::InvalidOperands(
                    "flat matrix cells must be numeric scalars",
                ));
            };
            if let Some(cell) = cell.as_real() {
                Ok(Z3Object::Z3(cell.into()))
            } else if let Some(cell) = cell.as_int() {
                Ok(Z3Object::Z3(Real::from_int(&cell).into()))
            } else {
                Err(ToZ3Error::InvalidOperands(
                    "flat matrix cells must be numeric scalars",
                ))
            }
        })
        .collect::<Result<_, _>>()?;
    Ok(Z3Object::Matrix(Matrix {
        rows: matrix.rows,
        cols: matrix.cols,
        elements,
    }))
}

fn lower_boolean<Metadata: MaybeTyped + Clone>(
    environment: &Environment,
    expression: &Expr<Metadata>,
) -> Result<Bool, ToZ3Error> {
    let Z3Object::Z3(expression) = lower(environment, expression)? else {
        return Err(ToZ3Error::InvalidOperands(
            "logical operations require Boolean operands",
        ));
    };
    expression.as_bool().ok_or(ToZ3Error::InvalidOperands(
        "logical operations require Boolean operands",
    ))
}

fn lower_boolean_finite<Metadata: MaybeTyped + Clone>(
    environment: &Environment,
    expressions: &[Expr<Metadata>],
    op: Finop,
) -> Result<Z3Object, ToZ3Error> {
    if expressions.is_empty() {
        return Err(ToZ3Error::Empty(match op {
            Finop::And => "conjunction requires at least one operand",
            Finop::Or => "disjunction requires at least one operand",
            _ => unreachable!("lower_boolean_finite only accepts Boolean finite operators"),
        }));
    }
    let expressions = expressions
        .iter()
        .map(|expression| lower_boolean(environment, expression))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Z3Object::Z3(match op {
        Finop::And => Bool::and(&expressions).into(),
        Finop::Or => Bool::or(&expressions).into(),
        _ => unreachable!("lower_boolean_finite only accepts Boolean finite operators"),
    }))
}

fn lower_logic_chain<Metadata: MaybeTyped + Clone>(
    environment: &Environment,
    chain: &LogicChain<Metadata>,
) -> Result<Z3Object, ToZ3Error> {
    match chain.assertions.as_slice() {
        [] => Ok(Z3Object::Z3(
            lower_boolean(environment, &chain.start)?.into(),
        )),
        [(Logic::Imp, consequent)] => Ok(Z3Object::Z3(
            lower_boolean(environment, &chain.start)?
                .implies(lower_boolean(environment, consequent)?)
                .into(),
        )),
        [(Logic::Iff, _)] => Err(ToZ3Error::Unsupported(
            "biconditional must be lowered before to_z3",
        )),
        _ => Err(ToZ3Error::Unsupported(
            "multi-edge logic chains must be lowered before to_z3",
        )),
    }
}

fn lower_typed_name(name: String, ty: &Type) -> Result<Z3Object, ToZ3Error> {
    Ok(match ty {
        Type::Bool => Z3Object::Z3(Bool::new_const(name).into()),
        Type::Nat | Type::Int => Z3Object::Z3(Int::new_const(name).into()),
        Type::Real => Z3Object::Z3(Real::new_const(name).into()),
        Type::Matrix(_, _) | Type::Seq(_) => {
            return Err(ToZ3Error::Unsupported(
                "nonscalar variables must be elaborated before Z3 lowering",
            ));
        }
    })
}

fn lower_cmp_chain<Metadata: MaybeTyped + Clone>(
    γ: &Environment,
    chain: &CmpChain<Metadata>,
) -> Result<Z3Object, ToZ3Error> {
    if chain.assertions.is_empty() {
        return Err(ToZ3Error::Empty(
            "comparison chain requires at least one assertion",
        ));
    }
    let mut previous = lower(γ, &chain.start)?;
    let mut comparisons = Vec::with_capacity(chain.assertions.len());
    for (comparison, current) in &chain.assertions {
        let current = lower(γ, current)?;
        comparisons.push(compare(previous, *comparison, current.clone())?);
        previous = current;
    }
    let result = if comparisons.len() == 1 {
        comparisons.pop().unwrap()
    } else {
        Bool::and(&comparisons)
    };
    Ok(Z3Object::Z3(result.into()))
}

fn lower_finite<Metadata: MaybeTyped + Clone>(
    γ: &Environment,
    expressions: &[Expr<Metadata>],
    operation: fn(Z3Object, Z3Object) -> Result<Z3Object, ToZ3Error>,
    name: &str,
) -> Result<Z3Object, ToZ3Error> {
    let mut expressions = expressions.iter().map(|expression| lower(γ, expression));
    let first = expressions.next().ok_or(ToZ3Error::Empty(match name {
        "addition" => "addition requires at least one operand",
        _ => "multiplication requires at least one operand",
    }))??;
    expressions.try_fold(first, |left, right| operation(left, right?))
}

impl Display for Z3Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z3Object::Matrix(_matrix) => {
                todo!("s-expression representing list of rows of fmt'ed z3 objects")
            }
            Z3Object::Z3(dynamic) => dynamic.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use expect_test::expect;
    use ratex_parser::parse;
    use z3::{
        SatResult, Solver, SortKind,
        ast::{Bool, Int, Real},
    };

    use crate::{
        Binop, Cmp, CmpChain, Expr, Finop, ImplicitDimension, Matrix, Monop, NaturalParameter,
        RawExpr, SeqType, Type, TypeExpr, Variable,
        elaboration::ElaborationError,
        from_tex,
        preprocessing::prepare_expression,
        to_z3::{ToZ3Error, ToZ3Result, Z3Object, to_z3 as prepared_to_z3},
        type_resolver::{
            OperatorTypeRules, SymbolicTypeEnvironment, TypeResolver, TypedMetadata, type_expr,
        },
        visit_mut::VisitContext,
    };

    #[derive(Clone, Default)]
    struct Environment {
        types: HashMap<Variable, Type>,
        equalities: HashMap<Expr<()>, u64>,
        implicit_dimensions: HashMap<ImplicitDimension, u64>,
    }

    impl Environment {
        fn symbolic_types(&self) -> SymbolicTypeEnvironment {
            let mut types = self
                .types
                .iter()
                .map(|(variable, ty)| (variable.clone(), type_expr(ty.clone())))
                .collect::<HashMap<_, _>>();
            for expression in self.equalities.keys() {
                if let RawExpr::Variable(variable) = &expression.raw {
                    types.entry(variable.clone()).or_insert(TypeExpr::Nat);
                }
            }
            SymbolicTypeEnvironment { types }
        }

        fn assignment(&self) -> crate::Environment {
            let mut natural_assignment = self
                .implicit_dimensions
                .iter()
                .map(|(dimension, value)| (NaturalParameter::ImplicitDimension(*dimension), *value))
                .collect::<HashMap<_, _>>();
            for (expression, value) in &self.equalities {
                if let RawExpr::Variable(variable) = &expression.raw {
                    natural_assignment.insert(NaturalParameter::Variable(variable.clone()), *value);
                }
            }
            crate::Environment { natural_assignment }
        }
    }

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
        active_ranges: Vec::new(),
    };

    const NEGATIVE: VisitContext = VisitContext {
        logical_polarity: false,
        active_ranges: Vec::new(),
    };

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
    }

    fn lower_to_z3<Metadata>(
        environment: &Environment,
        expression: &Expr<Metadata>,
        context: VisitContext,
    ) -> Result<ToZ3Result, ToZ3Error> {
        let prepared = prepare_expression(&environment.symbolic_types(), expression, context)?;
        prepared_to_z3(&environment.assignment(), &prepared)
    }

    fn to_z3<Metadata: Clone>(environment: Environment, expression: Expr<Metadata>) -> Z3Object {
        lower_to_z3(&environment, &expression, POSITIVE)
            .unwrap()
            .expression
    }

    fn assert_lowering_error<Metadata: Clone>(
        environment: Environment,
        expression: Expr<Metadata>,
        expected: ToZ3Error,
    ) {
        let actual = match lower_to_z3(&environment, &expression, POSITIVE) {
            Ok(_) => panic!("lowering unexpectedly succeeded"),
            Err(error) => error,
        };
        let elaborated = match expected.clone() {
            ToZ3Error::Type(error) => Some(ElaborationError::Type(error)),
            ToZ3Error::Natural(error) => Some(ElaborationError::Natural(error)),
            ToZ3Error::Unsupported(message) => Some(ElaborationError::Unsupported(message)),
            ToZ3Error::InvalidOperands(message) => Some(ElaborationError::InvalidOperands(message)),
            ToZ3Error::Shape(message) => Some(ElaborationError::Shape(message)),
            ToZ3Error::Empty(message) => Some(ElaborationError::Empty(message)),
            ToZ3Error::DimensionOverflow => Some(ElaborationError::DimensionOverflow),
            ToZ3Error::InvalidMatrixLiteral => Some(ElaborationError::InvalidMatrixLiteral),
            ToZ3Error::Elaboration(_) => None,
        };
        assert!(
            actual == expected
                || elaborated.is_some_and(|error| actual == ToZ3Error::Elaboration(error)),
            "unexpected lowering error: {actual:?}"
        );
    }

    fn scalar(environment: Environment, expression: Expr<()>) -> z3::ast::Dynamic {
        match to_z3(environment, expression) {
            Z3Object::Z3(expression) => expression,
            Z3Object::Matrix(_) => panic!("expected a scalar Z3 expression"),
        }
    }

    fn matrix(environment: Environment, expression: Expr<()>) -> Matrix<Z3Object> {
        match to_z3(environment, expression) {
            Z3Object::Matrix(matrix) => matrix,
            Z3Object::Z3(_) => panic!("expected a matrix Z3 expression"),
        }
    }

    fn matrix_strings(matrix: &Matrix<Z3Object>) -> Vec<String> {
        matrix.elements.iter().map(ToString::to_string).collect()
    }

    fn assert_scalar_value(environment: Environment, expression: Expr<()>, expected: i64) {
        let value = scalar(environment, expression);
        let expected = Int::from_i64(expected);
        let equality = if let Some(value) = value.as_int() {
            value.eq(expected)
        } else if let Some(value) = value.as_real() {
            value.eq(z3::ast::Real::from_int(&expected))
        } else {
            panic!("expected a numeric scalar")
        };
        let solver = Solver::new();
        solver.assert(equality.not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_variable_sorts() {
        for (name, τ, expected_sort) in [
            ("b", Type::Bool, SortKind::Bool),
            ("n", Type::Nat, SortKind::Int),
            ("i", Type::Int, SortKind::Int),
            ("x", Type::Real, SortKind::Real),
        ] {
            let variable = Variable::new(name);
            let environment = Environment {
                types: [(variable.clone(), τ)].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: [].into_iter().collect(),
            };

            assert_eq!(
                scalar(environment, Expr::new(RawExpr::Variable(variable))).sort_kind(),
                expected_sort,
            );
        }
    }

    #[test]
    fn test_natural_literal() {
        expect!["42"].assert_eq(
            &scalar(Environment::default(), Expr::new(RawExpr::NatLiteral(42))).to_string(),
        );
    }

    #[test]
    fn test_context_dependent_matrix_constants() {
        let identity = expression("I");
        let basis = expression("e_2");
        let zero = expression(r"\mathbb{0}");
        let RawExpr::IdentityMatrix {
            dimension: identity_dimension,
        } = identity.raw
        else {
            panic!("expected identity matrix")
        };
        let RawExpr::StandardBasis {
            dimension: basis_dimension,
            ..
        } = basis.raw
        else {
            panic!("expected standard basis vector")
        };
        let RawExpr::ZeroMatrix {
            rows: zero_rows,
            cols: zero_cols,
        } = zero.raw
        else {
            panic!("expected zero matrix")
        };
        let environment = || Environment {
            types: HashMap::new(),
            equalities: HashMap::new(),
            implicit_dimensions: HashMap::from([
                (identity_dimension, 2),
                (basis_dimension, 3),
                (zero_rows, 2),
                (zero_cols, 3),
            ]),
        };

        assert_eq!(
            matrix_strings(&matrix(environment(), identity)),
            ["(to_real 1)", "(to_real 0)", "(to_real 0)", "(to_real 1)"]
        );
        assert_eq!(
            matrix_strings(&matrix(environment(), basis)),
            ["(to_real 0)", "(to_real 1)", "(to_real 0)"]
        );
        assert_eq!(
            matrix_strings(&matrix(environment(), zero)),
            [
                "(to_real 0)",
                "(to_real 0)",
                "(to_real 0)",
                "(to_real 0)",
                "(to_real 0)",
                "(to_real 0)"
            ]
        );
    }

    #[test]
    fn test_implicit_matrix_dimension_must_be_present() {
        let identity = expression("I");
        let RawExpr::IdentityMatrix { dimension } = identity.raw else {
            panic!("expected identity matrix")
        };
        assert_lowering_error(
            Environment::default(),
            identity,
            ToZ3Error::Elaboration(ElaborationError::Natural(
                crate::NaturalEvaluationError::MissingAssignment(
                    NaturalParameter::ImplicitDimension(dimension),
                ),
            )),
        );
    }

    #[test]
    fn test_sequence_operations_expand_exactly_the_selected_terms() {
        let sequence = Variable::new("z");
        let environment = || Environment {
            types: HashMap::from([(
                sequence.clone(),
                Type::Seq(Box::new(SeqType {
                    t: Type::Real,
                    n: 3,
                })),
            )]),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::from([(expression("n"), 3)]),
        };
        expect!["(+ |z_{2}| |z_{3}|)\n(* |z_{2}| |z_{3}|)"].assert_eq(&format!(
            "{}\n{}",
            scalar(environment(), expression(r"\sum_{i=2}^{n} z_i")),
            scalar(environment(), expression(r"\prod_{i=2}^{n} z_i")),
        ));
    }

    #[test]
    fn test_sequence_diagonalization_lowers_to_scalar_cells() {
        let sequence = Variable::new("z");
        let diagonal = matrix(
            Environment {
                types: HashMap::from([(
                    sequence,
                    Type::Seq(Box::new(SeqType {
                        t: Type::Real,
                        n: 3,
                    })),
                )]),
                ..Environment::default()
            },
            expression(r"\operatorname{diag}(z)"),
        );
        assert_eq!((diagonal.rows, diagonal.cols), (3, 3));
        let cells = matrix_strings(&diagonal);
        for row in 0..3 {
            for col in 0..3 {
                let cell = &cells[row * 3 + col];
                if row == col {
                    assert_eq!(cell, &format!("|z_{{{}}}|", row + 1));
                } else {
                    assert_eq!(cell, "(to_real 0)");
                }
            }
        }
    }

    #[test]
    fn test_sequence_index_must_be_in_bounds() {
        let sequence = Variable::new("z");
        assert_lowering_error(
            Environment {
                types: HashMap::from([(
                    sequence,
                    Type::Seq(Box::new(SeqType {
                        t: Type::Real,
                        n: 2,
                    })),
                )]),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            expression("z_3"),
            ToZ3Error::InvalidOperands("sequence index is outside its one-based bounds"),
        );
    }

    #[test]
    fn test_matrix_sequence_product_uses_only_selected_terms() {
        let sequence = Variable::new("A");
        let environment = Environment {
            types: HashMap::from([(
                sequence,
                Type::Seq(Box::new(SeqType {
                    t: Type::Matrix(2, 2),
                    n: 3,
                })),
            )]),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };
        let product = matrix(environment, expression(r"\prod_{i=2}^{3} A_i"));
        assert_eq!((product.rows, product.cols), (2, 2));
        for cell in matrix_strings(&product) {
            assert!(cell.contains("A_{2}"));
            assert!(cell.contains("A_{3}"));
            assert!(!cell.contains("A_{1}"));
        }
    }

    #[test]
    fn test_hole_is_not_lowered() {
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Hole),
            ToZ3Error::Unsupported("holes are not supported by to_z3"),
        );
    }

    #[test]
    fn test_type_expression_is_not_lowered() {
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Type(TypeExpr::Real)),
            ToZ3Error::Unsupported("type expressions are not supported by to_z3"),
        );
    }

    #[test]
    fn test_real_and_one_by_one_matrix_casts() {
        let matrix_variable = Variable::new("A");
        let real_variable = Variable::new("x");
        let matrix_environment = Environment {
            types: HashMap::from([(matrix_variable, Type::Matrix(1, 1))]),
            ..Environment::default()
        };
        let real_environment = Environment {
            types: HashMap::from([(real_variable, Type::Real)]),
            ..Environment::default()
        };

        let extracted = scalar(
            matrix_environment,
            expression(r"\operatorname{cast}(\mathbb{R}, A)"),
        );
        assert_eq!(extracted.sort_kind(), SortKind::Real);
        assert!(extracted.to_string().contains("A_{1,1}"));

        let unchanged = scalar(
            real_environment,
            expression(r"\operatorname{cast}(\mathbb{R}, x)"),
        );
        assert_eq!(unchanged.sort_kind(), SortKind::Real);
        assert_eq!(unchanged.to_string(), "x");
    }

    #[test]
    fn test_real_cast_to_symbolic_one_by_one_matrix() {
        let target = Expr::new(RawExpr::Type(TypeExpr::Matrix(
            expression("m"),
            expression("n"),
        )));
        let cast = Expr::new(RawExpr::Binop(Binop::Cast, target, expression("x")));
        let environment = Environment {
            types: HashMap::from([(Variable::new("x"), Type::Real)]),
            equalities: HashMap::from([(expression("m"), 1), (expression("n"), 1)]),
            implicit_dimensions: HashMap::new(),
        };
        let cast = matrix(environment, cast);
        assert_eq!((cast.rows, cast.cols), (1, 1));
        assert_eq!(matrix_strings(&cast), ["x"]);
    }

    #[test]
    fn test_invalid_casts_return_errors() {
        let matrix_variable = Variable::new("A");
        assert_lowering_error(
            Environment {
                types: HashMap::from([(matrix_variable, Type::Matrix(2, 2))]),
                ..Environment::default()
            },
            expression(r"\operatorname{cast}(\mathbb{R}, A)"),
            ToZ3Error::InvalidOperands(
                "a cast to real requires a real scalar or real-valued 1x1 matrix",
            ),
        );
        assert_lowering_error(
            Environment {
                types: HashMap::from([(Variable::new("n"), Type::Nat)]),
                ..Environment::default()
            },
            expression(r"\operatorname{cast}(\mathbb{R}, n)"),
            ToZ3Error::InvalidOperands(
                "a cast to real requires a real scalar or real-valued 1x1 matrix",
            ),
        );
        assert_lowering_error(
            Environment {
                types: HashMap::from([(Variable::new("x"), Type::Real)]),
                ..Environment::default()
            },
            expression(r"\operatorname{cast}(\mathbb{N}, x)"),
            ToZ3Error::Unsupported("only real and 1x1 matrix casts are supported"),
        );

        let matrix_target = |rows, cols| {
            Expr::new(RawExpr::Type(TypeExpr::Matrix(
                expression(rows),
                expression(cols),
            )))
        };
        let value = || expression("x");
        let environment = || Environment {
            types: HashMap::from([(Variable::new("x"), Type::Real)]),
            ..Environment::default()
        };
        assert_lowering_error(
            environment(),
            Expr::new(RawExpr::Binop(
                Binop::Cast,
                matrix_target("2", "1"),
                value(),
            )),
            ToZ3Error::Shape("a real scalar can only be cast to a 1x1 matrix"),
        );
        assert_lowering_error(
            environment(),
            Expr::new(RawExpr::Binop(
                Binop::Cast,
                matrix_target("m", "n"),
                value(),
            )),
            ToZ3Error::Natural(crate::NaturalEvaluationError::MissingAssignment(
                NaturalParameter::Variable(Variable::new("m")),
            )),
        );
        assert_lowering_error(
            environment(),
            Expr::new(RawExpr::Binop(Binop::Cast, expression("T"), value())),
            ToZ3Error::InvalidOperands("cast target must be a type expression"),
        );
    }

    #[test]
    #[should_panic(expected = "has no symbolically inferred type")]
    fn test_missing_variable_type_is_an_invariant_failure() {
        let variable = Variable::new("x");
        let expression = Expr::<()>::new(RawExpr::Variable(variable));
        let _ = lower_to_z3(&Environment::default(), &expression, POSITIVE);
    }

    #[test]
    fn test_empty_finite_operation_returns_an_error() {
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Finop(Finop::Plus, vec![])),
            ToZ3Error::Empty("addition requires at least one operand"),
        );
    }

    #[test]
    fn test_boolean_finite_operations_and_single_implication() {
        let environment = Environment {
            types: ["p", "q", "r"]
                .into_iter()
                .map(|name| (Variable::new(name), Type::Bool))
                .collect(),
            ..Environment::default()
        };
        let actual = scalar(
            environment,
            expression(r"p \land (q \lor r) \land (p \implies q)"),
        )
        .as_bool()
        .unwrap();
        let p = Bool::new_const("p");
        let q = Bool::new_const("q");
        let r = Bool::new_const("r");
        let expected = Bool::and(&[p.clone(), Bool::or(&[q.clone(), r]), p.implies(q)]);
        let solver = Solver::new();
        solver.assert(actual.eq(expected).not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_invalid_boolean_operations_return_errors() {
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Finop(Finop::And, Vec::new())),
            ToZ3Error::Empty("conjunction requires at least one operand"),
        );
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Finop(
                Finop::Or,
                vec![Expr::new(RawExpr::NatLiteral(1))],
            )),
            ToZ3Error::InvalidOperands("logical operations require Boolean operands"),
        );
    }

    #[test]
    fn test_forall_is_retained_but_not_lowered_to_z3() {
        let environment = Environment {
            types: [(Variable::new("p"), Type::Bool)].into_iter().collect(),
            ..Environment::default()
        };
        assert_lowering_error(
            environment.clone(),
            expression(r"\forall p, p"),
            ToZ3Error::Elaboration(ElaborationError::Unsupported(
                "finite operator remains after concrete elaboration",
            )),
        );
        assert_lowering_error(
            environment,
            expression(r"\exists p, p"),
            ToZ3Error::Elaboration(ElaborationError::Unsupported(
                "finite operator remains after concrete elaboration",
            )),
        );
    }

    #[test]
    fn test_public_lowering_preprocesses_logic_chains() {
        let environment = Environment {
            types: ["p", "q", "r"]
                .into_iter()
                .map(|name| (Variable::new(name), Type::Bool))
                .collect(),
            ..Environment::default()
        };
        let actual = scalar(environment, expression(r"p \iff q \implies r"))
            .as_bool()
            .unwrap();
        let p = Bool::new_const("p");
        let q = Bool::new_const("q");
        let r = Bool::new_const("r");
        let expected = Bool::and(&[
            p.clone().implies(q.clone()),
            q.clone().implies(p),
            q.implies(r),
        ]);
        let solver = Solver::new();
        solver.assert(actual.eq(expected).not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_core_lowering_rejects_unprocessed_logic_chains() {
        let environment = Environment {
            types: ["p", "q", "r"]
                .into_iter()
                .map(|name| (Variable::new(name), Type::Bool))
                .collect(),
            ..Environment::default()
        };
        let types = environment.symbolic_types();
        let runtime = environment.assignment();
        let rules = OperatorTypeRules::core();
        let mut iff = expression(r"p \iff q").with_default_metadata::<TypedMetadata>();
        TypeResolver::new(&types, &rules)
            .resolve(&mut iff, POSITIVE)
            .unwrap();
        let mut implications =
            expression(r"p \implies q \implies r").with_default_metadata::<TypedMetadata>();
        TypeResolver::new(&types, &rules)
            .resolve(&mut implications, POSITIVE)
            .unwrap();
        assert_eq!(
            super::lower(&runtime, &iff).err(),
            Some(ToZ3Error::Unsupported(
                "biconditional must be lowered before to_z3"
            ))
        );
        assert_eq!(
            super::lower(&runtime, &implications).err(),
            Some(ToZ3Error::Unsupported(
                "multi-edge logic chains must be lowered before to_z3"
            ))
        );
    }

    #[test]
    fn test_negative_polarity_does_not_negate_the_result() {
        let environment = Environment {
            types: [(Variable::new("p"), Type::Bool)].into_iter().collect(),
            ..Environment::default()
        };
        let expression = expression("p");
        let Z3Object::Z3(positive) = lower_to_z3(&environment, &expression, POSITIVE)
            .unwrap()
            .expression
        else {
            panic!("expected a Boolean scalar")
        };
        let positive = positive.as_bool().unwrap();
        let Z3Object::Z3(negative) = lower_to_z3(&environment, &expression, NEGATIVE)
            .unwrap()
            .expression
        else {
            panic!("expected a Boolean scalar")
        };
        let negative = negative.as_bool().unwrap();
        let solver = Solver::new();
        solver.assert(positive.eq(negative).not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_incompatible_element_of_is_false() {
        let membership = Expr::<()>::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(Variable::new("x"))),
            Expr::new(RawExpr::Type(TypeExpr::Real)),
        ));
        assert_eq!(
            scalar(
                Environment {
                    types: HashMap::from([(Variable::new("x"), Type::Matrix(2, 2),)]),
                    ..Environment::default()
                },
                membership,
            )
            .to_string(),
            "(not (= 0 0))"
        );
    }

    #[test]
    fn test_symbolic_matrix_membership_uses_concrete_environment_dimensions() {
        let a = Variable::new("A");
        let n = Variable::new("n");
        let d = Variable::new("d");
        let p = Variable::new("p");
        let environment = |p_value| Environment {
            types: [
                (a.clone(), Type::Matrix(3, 8)),
                (n.clone(), Type::Nat),
                (d.clone(), Type::Nat),
                (p.clone(), Type::Nat),
            ]
            .into_iter()
            .collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::from([
                (Expr::new(RawExpr::Variable(n.clone())), 3),
                (Expr::new(RawExpr::Variable(d.clone())), 4),
                (Expr::new(RawExpr::Variable(p.clone())), p_value),
            ]),
        };
        let variable = |variable| Expr::new(RawExpr::Variable(variable));
        let membership = Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            variable(a.clone()),
            Expr::new(RawExpr::Type(TypeExpr::Matrix(
                variable(n.clone()),
                Expr::new(RawExpr::Finop(
                    Finop::Plus,
                    vec![variable(d.clone()), variable(p.clone())],
                )),
            ))),
        ));
        let assertion = scalar(environment(4), membership.clone())
            .as_bool()
            .unwrap();
        let solver = Solver::new();
        solver.assert(assertion);
        assert_eq!(solver.check(), SatResult::Sat);
        let solver = Solver::new();
        solver.assert(scalar(environment(5), membership).as_bool().unwrap());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_negation() {
        expect!["(- 7)"].assert_eq(
            &scalar(
                Environment::default(),
                Expr::new(RawExpr::Monop(
                    Monop::Neg,
                    Expr::new(RawExpr::NatLiteral(7)),
                )),
            )
            .to_string(),
        );
    }

    #[test]
    fn test_trace_of_symbolic_literal_and_mixed_matrices() {
        let a = Variable::new("A");
        let environment = Environment {
            types: HashMap::from([(a, Type::Matrix(2, 2))]),
            ..Environment::default()
        };
        expect!["(+ |A_{1,1}| |A_{2,2}|)"]
            .assert_eq(&scalar(environment, expression(r"\operatorname{tr}(A)")).to_string());
        assert_scalar_value(
            Environment::default(),
            expression(r"\operatorname{tr}(\begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix})"),
            5,
        );

        let x = Variable::new("x");
        let mixed = scalar(
            Environment {
                types: HashMap::from([(x, Type::Real)]),
                ..Environment::default()
            },
            expression(r"\operatorname{tr}(\begin{bmatrix}x & 2 \\ 3 & 4\end{bmatrix})"),
        );
        assert_eq!(mixed.sort_kind(), SortKind::Real);
    }

    #[test]
    fn test_determinants_of_small_matrices() {
        for (matrix, expected) in [
            (r"\begin{bmatrix}7\end{bmatrix}", 7),
            (r"\begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix}", -2),
            (
                r"\begin{bmatrix}1 & 2 & 3 \\ 0 & 1 & 4 \\ 5 & 6 & 0\end{bmatrix}",
                1,
            ),
        ] {
            assert_scalar_value(
                Environment::default(),
                expression(&format!(r"\det({matrix})")),
                expected,
            );
        }

        let x = Variable::new("x");
        let mixed = scalar(
            Environment {
                types: HashMap::from([(x, Type::Real)]),
                ..Environment::default()
            },
            expression(r"\det(\begin{bmatrix}x & 2 \\ 3 & 4\end{bmatrix})"),
        );
        assert_eq!(mixed.sort_kind(), SortKind::Real);
    }

    #[test]
    fn test_trace_and_determinant_of_identity_and_zero() {
        let identity = expression("I");
        let zero = expression(r"\mathbb{0}");
        let RawExpr::IdentityMatrix {
            dimension: identity_dimension,
        } = identity.raw
        else {
            panic!("expected identity matrix")
        };
        let RawExpr::ZeroMatrix { rows, cols } = zero.raw else {
            panic!("expected zero matrix")
        };
        let environment = || Environment {
            implicit_dimensions: HashMap::from([(identity_dimension, 2), (rows, 2), (cols, 2)]),
            ..Environment::default()
        };
        let unary = |op, inner| Expr::new(RawExpr::Monop(op, inner));

        assert_scalar_value(environment(), unary(Monop::Trace, identity.clone()), 2);
        assert_scalar_value(environment(), unary(Monop::Det, identity), 1);
        assert_scalar_value(environment(), unary(Monop::Trace, zero.clone()), 0);
        assert_scalar_value(environment(), unary(Monop::Det, zero), 0);
    }

    #[test]
    fn test_trace_and_determinant_reject_invalid_operands() {
        for (tex, error) in [
            (
                r"\operatorname{tr}(1)",
                ToZ3Error::InvalidOperands("trace requires a matrix"),
            ),
            (
                r"\det(1)",
                ToZ3Error::InvalidOperands("determinant requires a matrix"),
            ),
            (
                r"\operatorname{tr}(\begin{bmatrix}1 & 2\end{bmatrix})",
                ToZ3Error::Shape("trace requires a square matrix"),
            ),
            (
                r"\det(\begin{bmatrix}1 & 2\end{bmatrix})",
                ToZ3Error::Shape("determinant requires a square matrix"),
            ),
            (
                r"\operatorname{tr}(\begin{bmatrix}\end{bmatrix})",
                ToZ3Error::Empty("trace requires a nonempty matrix"),
            ),
            (
                r"\det(\begin{bmatrix}\end{bmatrix})",
                ToZ3Error::Empty("determinant requires a nonempty matrix"),
            ),
        ] {
            assert_lowering_error(Environment::default(), expression(tex), error);
        }

        let boolean: Expr<()> = Expr::new(RawExpr::CmpChain(CmpChain {
            start: Expr::new(RawExpr::NatLiteral(1)),
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(1)))],
        }));
        for (op, cell) in [(Monop::Trace, boolean.clone()), (Monop::Det, boolean)] {
            assert_lowering_error(
                Environment::default(),
                Expr::new(RawExpr::Monop(
                    op,
                    Expr::new(RawExpr::Matrix(Matrix {
                        rows: 1,
                        cols: 1,
                        elements: vec![cell],
                    })),
                )),
                ToZ3Error::Type(crate::type_resolver::TypeError::Invalid(
                    "block matrix cells must be numeric scalars or matrices",
                )),
            );
        }

        for op in [Monop::Trace, Monop::Det] {
            assert_lowering_error(
                Environment::default(),
                Expr::<()>::new(RawExpr::Monop(
                    op,
                    Expr::new(RawExpr::Matrix(Matrix {
                        rows: 2,
                        cols: 2,
                        elements: vec![Expr::new(RawExpr::NatLiteral(1))],
                    })),
                )),
                ToZ3Error::Type(crate::type_resolver::TypeError::Invalid(
                    "matrix element count does not match its dimensions",
                )),
            );
        }
    }

    #[test]
    fn test_addition_and_multiplication() {
        let product = Expr::new(RawExpr::Finop(
            Finop::Times,
            vec![
                Expr::new(RawExpr::NatLiteral(3)),
                Expr::new(RawExpr::NatLiteral(4)),
            ],
        ));
        let sum = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![Expr::new(RawExpr::NatLiteral(2)), product],
        ));

        expect!["(+ 2 (* 3 4))"].assert_eq(&scalar(Environment::default(), sum).to_string());
    }

    #[test]
    fn test_division() {
        let quotient = Expr::new(RawExpr::Binop(
            Binop::Div,
            Expr::new(RawExpr::NatLiteral(8)),
            Expr::new(RawExpr::NatLiteral(2)),
        ));

        expect!["(div 8 2)"].assert_eq(&scalar(Environment::default(), quotient).to_string());
    }

    #[test]
    fn test_mixed_numeric_operations_promote_to_real() {
        let x = Variable::new("x");
        let environment = || Environment {
            types: [(x.clone(), Type::Real)].into_iter().collect(),
            implicit_dimensions: HashMap::new(),
            equalities: [].into_iter().collect(),
        };
        let real = || Expr::new(RawExpr::Variable(x.clone()));
        let integer = || Expr::new(RawExpr::NatLiteral(2));

        let addition = Expr::new(RawExpr::Finop(Finop::Plus, vec![real(), integer()]));
        let multiplication = Expr::new(RawExpr::Finop(Finop::Times, vec![integer(), real()]));
        let division = Expr::new(RawExpr::Binop(Binop::Div, real(), integer()));

        expect!["(+ x (to_real 2))"].assert_eq(&scalar(environment(), addition).to_string());
        expect!["(* (to_real 2) x)"].assert_eq(&scalar(environment(), multiplication).to_string());
        expect!["(/ x (to_real 2))"].assert_eq(&scalar(environment(), division).to_string());
    }

    #[test]
    fn test_power_uses_known_exponent_equality() {
        let x = Variable::new("x");
        let n = Variable::new("n");
        let base = || Expr::new(RawExpr::Variable(x.clone()));
        let exponent = || Expr::with_metadata("exponent", RawExpr::Variable(n.clone()));
        let power = || {
            Expr::new(RawExpr::Binop(
                Binop::Power,
                base(),
                exponent().with_default_metadata(),
            ))
        };
        let environment = |value| Environment {
            types: [(x.clone(), Type::Int)].into_iter().collect(),
            implicit_dimensions: HashMap::new(),
            equalities: [(exponent().with_default_metadata(), value)]
                .into_iter()
                .collect(),
        };

        expect!["(* x x x)"].assert_eq(&scalar(environment(3), power()).to_string());
        expect!["x"].assert_eq(&scalar(environment(1), power()).to_string());
    }

    #[test]
    fn test_zero_power_uses_scalar_identity() {
        let x = Variable::new("x");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        let power: Expr<()> = Expr::new(RawExpr::Binop(
            Binop::Power,
            Expr::new(RawExpr::Variable(x.clone())),
            exponent.clone(),
        ));
        let environment = Environment {
            types: [(x, Type::Real)].into_iter().collect(),
            implicit_dimensions: HashMap::new(),
            equalities: [(exponent, 0)].into_iter().collect(),
        };

        expect!["(to_real 1)"].assert_eq(&scalar(environment, power).to_string());
    }

    #[test]
    fn test_power_requires_known_exponent_equality() {
        let power: Expr<()> = Expr::new(RawExpr::Binop(
            Binop::Power,
            Expr::new(RawExpr::NatLiteral(2)),
            Expr::new(RawExpr::Variable(Variable::new("n"))),
        ));

        assert_lowering_error(
            Environment {
                types: [(Variable::new("n"), Type::Nat)].into_iter().collect(),
                ..Environment::default()
            },
            power,
            ToZ3Error::Natural(crate::NaturalEvaluationError::MissingAssignment(
                NaturalParameter::Variable(Variable::new("n")),
            )),
        );
    }

    #[test]
    fn test_scalar_square_root_returns_principal_root_side_conditions() {
        let environment = Environment {
            types: HashMap::from([(Variable::new("x"), Type::Real)]),
            ..Environment::default()
        };
        let lowered = lower_to_z3(&environment, &expression(r"x^{\frac{1}{2}}"), POSITIVE).unwrap();

        assert_eq!(lowered.expression.to_string(), r"|x^{\\frac{1}{2}}|");
        assert_eq!(lowered.side_conditions.len(), 1);
        let condition = &lowered.side_conditions[0];
        assert_eq!(condition.introduced_variable.name, r"x^{\frac{1}{2}}");
        assert_eq!(condition.introduced_type, Type::Real);
        assert_eq!(condition.defining_assertions.len(), 2);
        assert!(matches!(
            condition.existence,
            super::LoweredExistence::Checkable(ref assertions) if assertions.len() == 1
        ));

        let solver = Solver::new();
        for assertion in &condition.defining_assertions {
            let Z3Object::Z3(assertion) = assertion else {
                panic!("square-root definition must be Boolean")
            };
            solver.assert(assertion.as_bool().unwrap());
        }
        solver.assert(Real::new_const("x").eq(Real::from_rational(4, 1)));
        solver.assert(
            Real::new_const(r"x^{\frac{1}{2}}")
                .eq(Real::from_rational(2, 1))
                .not(),
        );
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_two_norm_and_squared_two_norm_lower_through_core_operations() {
        let environment = Environment {
            types: HashMap::from([(Variable::new("v"), Type::Matrix(2, 1))]),
            ..Environment::default()
        };
        let norm = lower_to_z3(
            &environment,
            &expression(r"\left\lVert v \right\rVert_{2}"),
            POSITIVE,
        )
        .unwrap();
        assert_eq!(norm.side_conditions.len(), 1);
        assert!(matches!(
            norm.side_conditions[0].existence,
            super::LoweredExistence::Guaranteed
        ));

        let squared = lower_to_z3(
            &environment,
            &expression(r"\left\lVert v \right\rVert_{2}^{2}"),
            POSITIVE,
        )
        .unwrap();
        assert!(squared.side_conditions.is_empty());

        let entries = matrix(environment.clone(), expression("v")).elements;
        let Z3Object::Z3(norm_value) = norm.expression else {
            panic!("2-norm must lower to a scalar")
        };
        let Z3Object::Z3(squared_value) = squared.expression else {
            panic!("squared 2-norm must lower to a scalar")
        };
        let solver = Solver::new();
        for definition in &norm.side_conditions[0].defining_assertions {
            let Z3Object::Z3(definition) = definition else {
                panic!("norm definition must be Boolean")
            };
            solver.assert(definition.as_bool().unwrap());
        }
        for (entry, value) in entries.iter().zip([3, 4]) {
            let Z3Object::Z3(entry) = entry else {
                panic!("vector entry must be scalar")
            };
            solver.assert(entry.as_real().unwrap().eq(Real::from_rational(value, 1)));
        }
        solver.assert(
            norm_value
                .as_real()
                .unwrap()
                .eq(Real::from_rational(5, 1))
                .not(),
        );
        solver.assert(
            squared_value
                .as_real()
                .unwrap()
                .eq(Real::from_rational(25, 1))
                .not(),
        );
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_matrix_compound_and_repeated_square_roots() {
        let environment = Environment {
            types: HashMap::from([
                (Variable::new("A"), Type::Matrix(2, 2)),
                (Variable::new("x"), Type::Real),
            ]),
            ..Environment::default()
        };
        let matrix_root = lower_to_z3(
            &environment,
            &expression(r"A^{\frac{1}{2}} = A^{\frac{1}{2}}"),
            POSITIVE,
        )
        .unwrap();
        assert_eq!(matrix_root.side_conditions.len(), 1);
        assert_eq!(
            matrix_root.side_conditions[0].introduced_variable.name,
            r"A^{\frac{1}{2}}"
        );
        assert_eq!(
            matrix_root.side_conditions[0].introduced_type,
            Type::Matrix(2, 2)
        );
        assert!(matches!(
            matrix_root.side_conditions[0].existence,
            super::LoweredExistence::Assumed
        ));

        let compound = lower_to_z3(
            &environment,
            &expression(r"\left(x + 1\right)^{\frac{1}{2}}"),
            POSITIVE,
        )
        .unwrap();
        assert_eq!(compound.side_conditions.len(), 1);
        assert_eq!(
            compound.side_conditions[0].introduced_variable.name,
            r"\left(x + 1\right)^{\frac{1}{2}}"
        );

        let nested = lower_to_z3(
            &environment,
            &expression(r"\left(x^{\frac{1}{2}}\right)^{\frac{1}{2}}"),
            POSITIVE,
        )
        .unwrap();
        assert_eq!(nested.side_conditions.len(), 2);
    }

    #[test]
    fn test_matrix_variable_and_literal_lowering() {
        let a = Variable::new("A");
        let lowered = matrix(
            Environment {
                types: [(a.clone(), Type::Matrix(2, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::new(RawExpr::Variable(a)),
        );
        assert_eq!((lowered.rows, lowered.cols), (2, 2));
        assert_eq!(
            matrix_strings(&lowered),
            vec!["|A_{1,1}|", "|A_{1,2}|", "|A_{2,1}|", "|A_{2,2}|"]
        );
        assert!(lowered.elements.iter().all(
            |element| matches!(element, Z3Object::Z3(expression) if expression.as_real().is_some())
        ));

        let literal = matrix(
            Environment::default(),
            Expr::new(RawExpr::Matrix(Matrix {
                rows: 1,
                cols: 2,
                elements: vec![
                    Expr::new(RawExpr::NatLiteral(1)),
                    Expr::new(RawExpr::NatLiteral(2)),
                ],
            })),
        );
        assert_eq!(matrix_strings(&literal), vec!["(to_real 1)", "(to_real 2)"]);
    }

    #[test]
    fn test_block_matrix_lowering_flattens_typed_and_recursive_blocks() {
        let environment = Environment {
            types: HashMap::from([
                (Variable::new("A"), Type::Matrix(2, 2)),
                (Variable::new("b"), Type::Matrix(2, 1)),
                (Variable::new("c"), Type::Matrix(2, 1)),
                (Variable::new("d"), Type::Real),
            ]),
            ..Environment::default()
        };
        let block_tex = r"\begin{bmatrix}A & b \\ c^\top & d\end{bmatrix}";
        let block = matrix(environment.clone(), expression(block_tex));
        assert_eq!((block.rows, block.cols), (3, 3));
        assert_eq!(
            matrix_strings(&block),
            [
                "|A_{1,1}|",
                "|A_{1,2}|",
                "|b_{1,1}|",
                "|A_{2,1}|",
                "|A_{2,2}|",
                "|b_{2,1}|",
                "|c_{1,1}|",
                "|c_{2,1}|",
                "d",
            ]
        );

        let transposed = matrix(
            environment.clone(),
            expression(&format!(r"\left({block_tex}\right)^\top")),
        );
        assert_eq!(
            matrix_strings(&transposed),
            [
                "|A_{1,1}|",
                "|A_{2,1}|",
                "|c_{1,1}|",
                "|A_{1,2}|",
                "|A_{2,2}|",
                "|c_{2,1}|",
                "|b_{1,1}|",
                "|b_{2,1}|",
                "d",
            ]
        );

        let identity = r"\begin{bmatrix}1 & 0 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1\end{bmatrix}";
        let product = matrix(
            environment,
            expression(&format!(r"\left({block_tex}\right) {identity}")),
        );
        let inequalities = product
            .elements
            .iter()
            .zip(&block.elements)
            .map(|(actual, expected)| {
                let (Z3Object::Z3(actual), Z3Object::Z3(expected)) = (actual, expected) else {
                    panic!("flattened block cells must be scalar")
                };
                actual.eq(expected).not()
            })
            .collect::<Vec<_>>();
        let solver = Solver::new();
        solver.assert(Bool::or(&inequalities));
        assert_eq!(solver.check(), SatResult::Unsat);

        let recursive = expression(
            r"\begin{bmatrix}\begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix} & \begin{bmatrix}5 \\ 6\end{bmatrix} \\ \begin{bmatrix}7 & 8\end{bmatrix} & 9\end{bmatrix}",
        );
        assert_eq!(
            matrix_strings(&matrix(Environment::default(), recursive.clone())),
            [
                "(to_real 1)",
                "(to_real 2)",
                "(to_real 5)",
                "(to_real 3)",
                "(to_real 4)",
                "(to_real 6)",
                "(to_real 7)",
                "(to_real 8)",
                "(to_real 9)"
            ]
        );
        assert_scalar_value(
            Environment::default(),
            Expr::new(RawExpr::Monop(Monop::Trace, recursive.clone())),
            14,
        );
        assert_scalar_value(
            Environment::default(),
            Expr::new(RawExpr::Monop(Monop::Det, recursive)),
            -2,
        );
    }

    #[test]
    fn test_block_matrix_lowering_rejects_incompatible_blocks() {
        for (tex, environment, expected) in [
            (
                r"\begin{bmatrix}A & b\end{bmatrix}",
                Environment {
                    types: HashMap::from([
                        (Variable::new("A"), Type::Matrix(2, 2)),
                        (Variable::new("b"), Type::Matrix(3, 1)),
                    ]),
                    ..Environment::default()
                },
                ToZ3Error::Shape("blocks in a block-matrix row must have equal heights"),
            ),
            (
                r"\begin{bmatrix}A \\ c^\top\end{bmatrix}",
                Environment {
                    types: HashMap::from([
                        (Variable::new("A"), Type::Matrix(2, 2)),
                        (Variable::new("c"), Type::Matrix(3, 1)),
                    ]),
                    ..Environment::default()
                },
                ToZ3Error::Shape("blocks in a block-matrix column must have equal widths"),
            ),
        ] {
            assert_lowering_error(environment, expression(tex), expected);
        }
    }

    #[test]
    fn test_matrix_negation_addition_and_scaling() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let environment = || Environment {
            types: [
                (a.clone(), Type::Matrix(1, 2)),
                (b.clone(), Type::Matrix(1, 2)),
            ]
            .into_iter()
            .collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };
        let variable = |variable| Expr::new(RawExpr::Variable(variable));

        let negated = matrix(
            environment(),
            Expr::new(RawExpr::Monop(Monop::Neg, variable(a.clone()))),
        );
        assert_eq!(
            matrix_strings(&negated),
            vec!["(- |A_{1,1}|)", "(- |A_{1,2}|)"]
        );

        let added = matrix(
            environment(),
            Expr::new(RawExpr::Finop(
                Finop::Plus,
                vec![variable(a.clone()), variable(b.clone())],
            )),
        );
        assert_eq!(
            matrix_strings(&added),
            vec!["(+ |A_{1,1}| |B_{1,1}|)", "(+ |A_{1,2}| |B_{1,2}|)"]
        );

        let scaled = matrix(
            environment(),
            Expr::<()>::new(RawExpr::Finop(
                Finop::Times,
                vec![Expr::new(RawExpr::NatLiteral(2)), variable(a)],
            )),
        );
        assert_eq!(
            matrix_strings(&scaled),
            vec!["(* (to_real 2) |A_{1,1}|)", "(* (to_real 2) |A_{1,2}|)"]
        );
    }

    #[test]
    fn test_matrix_multiplication() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let product = matrix(
            Environment {
                types: [
                    (a.clone(), Type::Matrix(2, 2)),
                    (b.clone(), Type::Matrix(2, 1)),
                ]
                .into_iter()
                .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::Finop(
                Finop::Times,
                vec![
                    Expr::new(RawExpr::Variable(a)),
                    Expr::new(RawExpr::Variable(b)),
                ],
            )),
        );

        assert_eq!((product.rows, product.cols), (2, 1));
        assert_eq!(
            matrix_strings(&product),
            vec![
                "(+ (* |A_{1,1}| |B_{1,1}|) (* |A_{1,2}| |B_{2,1}|))",
                "(+ (* |A_{2,1}| |B_{1,1}|) (* |A_{2,2}| |B_{2,1}|))"
            ]
        );
    }

    #[test]
    fn test_one_by_one_matrix_division() {
        let a = Variable::new("A");
        let quotient = scalar(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 1))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Div,
                Expr::new(RawExpr::Variable(a)),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
        );

        expect!["(/ |A_{1,1}| (to_real 2))"].assert_eq(&quotient.to_string());
    }

    #[test]
    fn test_matrix_zero_power_is_identity() {
        let a = Variable::new("A");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        let identity = matrix(
            Environment {
                types: [(a.clone(), Type::Matrix(2, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: [(exponent.clone(), 0)].into_iter().collect(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Variable(a)),
                exponent,
            )),
        );

        assert_eq!(
            matrix_strings(&identity),
            vec!["(to_real 1)", "(to_real 0)", "(to_real 0)", "(to_real 1)"]
        );

        let exponent = Expr::new(RawExpr::Variable(Variable::new("k")));
        let integer_identity = matrix(
            Environment {
                types: HashMap::new(),
                implicit_dimensions: HashMap::new(),
                equalities: [(exponent.clone(), 0)].into_iter().collect(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Matrix(Matrix {
                    rows: 2,
                    cols: 2,
                    elements: vec![
                        Expr::new(RawExpr::NatLiteral(1)),
                        Expr::new(RawExpr::NatLiteral(2)),
                        Expr::new(RawExpr::NatLiteral(3)),
                        Expr::new(RawExpr::NatLiteral(4)),
                    ],
                })),
                exponent,
            )),
        );
        assert_eq!(
            matrix_strings(&integer_identity),
            vec!["(to_real 1)", "(to_real 0)", "(to_real 0)", "(to_real 1)"]
        );
    }

    #[test]
    fn test_positive_matrix_power_uses_matrix_multiplication() {
        let a = Variable::new("A");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        let squared = matrix(
            Environment {
                types: [(a.clone(), Type::Matrix(2, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: [(exponent.clone(), 2)].into_iter().collect(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Variable(a)),
                exponent,
            )),
        );

        assert_eq!((squared.rows, squared.cols), (2, 2));
        assert_eq!(
            matrix_strings(&squared)[0],
            "(+ (* |A_{1,1}| |A_{1,1}|) (* |A_{1,2}| |A_{2,1}|))"
        );
    }

    #[test]
    fn test_non_square_matrix_power_returns_an_error() {
        let a = Variable::new("A");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        assert_lowering_error(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: [(exponent.clone(), 1)].into_iter().collect(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Variable(a)),
                exponent,
            )),
            ToZ3Error::Shape("matrix power requires a square matrix"),
        );
    }

    #[test]
    fn test_invalid_matrix_multiplication_returns_an_error() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let product: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Times,
            vec![
                Expr::new(RawExpr::Variable(a.clone())),
                Expr::new(RawExpr::Variable(b.clone())),
            ],
        ));
        assert_lowering_error(
            Environment {
                types: [
                    (a.clone(), Type::Matrix(2, 2)),
                    (b.clone(), Type::Matrix(1, 2)),
                ]
                .into_iter()
                .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            product,
            ToZ3Error::Shape("matrix multiplication requires compatible dimensions"),
        );
    }

    #[test]
    fn test_mismatched_matrix_addition_returns_an_error() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        assert_lowering_error(
            Environment {
                types: [
                    (a.clone(), Type::Matrix(1, 2)),
                    (b.clone(), Type::Matrix(2, 1)),
                ]
                .into_iter()
                .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::Finop(
                Finop::Plus,
                vec![
                    Expr::new(RawExpr::Variable(a)),
                    Expr::new(RawExpr::Variable(b)),
                ],
            )),
            ToZ3Error::Shape("matrix addition requires equal dimensions"),
        );
    }

    #[test]
    fn test_larger_matrix_division_returns_an_error() {
        let a = Variable::new("A");
        assert_lowering_error(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::Binop(
                Binop::Div,
                Expr::new(RawExpr::Variable(a)),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
            ToZ3Error::Shape("matrix division is only supported for 1x1 matrices"),
        );
    }

    #[test]
    fn test_comparison_chain_uses_written_order() {
        let variables: Vec<_> = ["a", "b", "c", "d", "e", "f"]
            .into_iter()
            .map(Variable::new)
            .collect();
        let expression =
            |index: usize| -> Expr<()> { Expr::new(RawExpr::Variable(variables[index].clone())) };
        let chain = Expr::new(RawExpr::CmpChain(CmpChain {
            start: expression(0),
            assertions: vec![
                (Cmp::Eq, expression(1)),
                (Cmp::Lt, expression(2)),
                (Cmp::Gt, expression(3)),
                (Cmp::Le, expression(4)),
                (Cmp::Ge, expression(5)),
            ],
        }));
        let environment = Environment {
            types: variables
                .into_iter()
                .map(|variable| (variable, Type::Int))
                .collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };

        expect!["(and (= a b) (< b c) (> c d) (<= d e) (>= e f))"]
            .assert_eq(&scalar(environment, chain).to_string());
    }

    #[test]
    fn test_comparison_promotes_integer_to_real() {
        let x = Variable::new("x");
        let chain = Expr::new(RawExpr::CmpChain(CmpChain {
            start: Expr::new(RawExpr::NatLiteral(2)),
            assertions: vec![(Cmp::Lt, Expr::new(RawExpr::Variable(x.clone())))],
        }));
        let environment = Environment {
            types: [(x, Type::Real)].into_iter().collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };

        expect!["(< (to_real 2) x)"].assert_eq(&scalar(environment, chain).to_string());
    }

    #[test]
    fn test_matrix_equality_is_elementwise() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let chain = Expr::new(RawExpr::CmpChain(CmpChain {
            start: Expr::new(RawExpr::Variable(a.clone())),
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::Variable(b.clone())))],
        }));
        let environment = Environment {
            types: [(a, Type::Matrix(1, 2)), (b, Type::Matrix(1, 2))]
                .into_iter()
                .collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };

        expect!["(and (= |A_{1,1}| |B_{1,1}|) (= |A_{1,2}| |B_{1,2}|))"]
            .assert_eq(&scalar(environment, chain).to_string());
    }

    #[test]
    fn test_matrix_inequality_negates_elementwise_equality() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let chain = Expr::new(RawExpr::CmpChain(CmpChain {
            start: Expr::new(RawExpr::Variable(a.clone())),
            assertions: vec![(Cmp::Ne, Expr::new(RawExpr::Variable(b.clone())))],
        }));
        let environment = Environment {
            types: [(a, Type::Matrix(1, 2)), (b, Type::Matrix(1, 2))]
                .into_iter()
                .collect(),
            implicit_dimensions: HashMap::new(),
            equalities: HashMap::new(),
        };

        expect!["(or (not (= |A_{1,1}| |B_{1,1}|)) (not (= |A_{1,2}| |B_{1,2}|)))"]
            .assert_eq(&scalar(environment, chain).to_string());
    }

    #[test]
    fn test_boolean_comparison_returns_an_error() {
        let p = Variable::new("P");
        let q = Variable::new("Q");
        assert_lowering_error(
            Environment {
                types: [(p.clone(), Type::Bool), (q.clone(), Type::Bool)]
                    .into_iter()
                    .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::Variable(p)),
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::Variable(q)))],
            })),
            ToZ3Error::InvalidOperands("boolean scalars cannot be compared"),
        );
    }

    #[test]
    fn test_mismatched_matrix_equality_returns_an_error() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        assert_lowering_error(
            Environment {
                types: [
                    (a.clone(), Type::Matrix(1, 2)),
                    (b.clone(), Type::Matrix(2, 1)),
                ]
                .into_iter()
                .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::Variable(a)),
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::Variable(b)))],
            })),
            ToZ3Error::Shape("matrix equality requires equal dimensions"),
        );
    }

    #[test]
    fn test_matrix_ordering_returns_an_error() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        assert_lowering_error(
            Environment {
                types: [
                    (a.clone(), Type::Matrix(1, 2)),
                    (b.clone(), Type::Matrix(1, 2)),
                ]
                .into_iter()
                .collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::Variable(a)),
                assertions: vec![(Cmp::Lt, Expr::new(RawExpr::Variable(b)))],
            })),
            ToZ3Error::InvalidOperands("matrix ordering comparisons are not supported"),
        );
    }

    #[test]
    fn test_scalar_matrix_comparison_returns_an_error() {
        let a = Variable::new("A");
        assert_lowering_error(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 2))].into_iter().collect(),
                implicit_dimensions: HashMap::new(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::NatLiteral(1)),
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::Variable(a)))],
            })),
            ToZ3Error::InvalidOperands("scalar-matrix comparisons are not supported"),
        );
    }

    #[test]
    fn test_empty_comparison_chain_returns_an_error() {
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::NatLiteral(1)),
                assertions: vec![],
            })),
            ToZ3Error::Empty("comparison chain requires at least one assertion"),
        );
    }
}
