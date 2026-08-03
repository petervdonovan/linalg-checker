use std::{
    error::Error,
    fmt::{self, Display},
    ops::{Add, Div, Mul, Neg},
};

use z3::ast::{Bool, Int, Real};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Matrix, Monop, RawExpr, Type, TypeExpr,
    Variable,
};

#[derive(Clone)]
pub enum Z3Object {
    Matrix(Matrix<Z3Object>),
    Z3(z3::ast::Dynamic),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToZ3Error {
    Unsupported(&'static str),
    MissingVariableType(Variable),
    MissingPowerExponent,
    InvalidOperands(&'static str),
    Shape(&'static str),
    Empty(&'static str),
    DimensionOverflow,
    InvalidMatrixLiteral,
}

impl Display for ToZ3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(message)
            | Self::InvalidOperands(message)
            | Self::Shape(message)
            | Self::Empty(message) => f.write_str(message),
            Self::MissingVariableType(variable) => {
                write!(
                    f,
                    "variable {} is missing from the type environment",
                    variable.z3_name()
                )
            }
            Self::MissingPowerExponent => {
                f.write_str("power exponent is missing from the equality environment")
            }
            Self::DimensionOverflow => f.write_str("matrix dimensions overflow usize"),
            Self::InvalidMatrixLiteral => {
                f.write_str("matrix element count does not match its dimensions")
            }
        }
    }
}

impl Error for ToZ3Error {}

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
            Self::Matrix(matrix) => Ok(Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(Neg::neg)
                    .collect::<Result<_, _>>()?,
            })),
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
            (Self::Matrix(left), Self::Matrix(right)) => {
                if left.rows != right.rows || left.cols != right.cols {
                    return Err(ToZ3Error::Shape(
                        "matrix addition requires equal dimensions",
                    ));
                }
                Ok(Self::Matrix(Matrix {
                    rows: left.rows,
                    cols: left.cols,
                    elements: left
                        .elements
                        .into_iter()
                        .zip(right.elements)
                        .map(|(left, right)| left + right)
                        .collect::<Result<_, _>>()?,
                }))
            }
            (Self::Matrix(_), Self::Z3(_)) | (Self::Z3(_), Self::Matrix(_)) => Err(
                ToZ3Error::InvalidOperands("scalar-matrix addition is not supported"),
            ),
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
            (Self::Matrix(left), Self::Matrix(right)) => multiply_matrices(left, right),
            (Self::Matrix(matrix), scalar @ Self::Z3(_)) => Ok(Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|element| element * scalar.clone())
                    .collect::<Result<_, _>>()?,
            })),
            (scalar @ Self::Z3(_), Self::Matrix(matrix)) => Ok(Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|element| scalar.clone() * element)
                    .collect::<Result<_, _>>()?,
            })),
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
            (Self::Matrix(left), Self::Matrix(right)) => single_cell(left)? / single_cell(right)?,
            (Self::Matrix(left), right @ Self::Z3(_)) => single_cell(left)? / right,
            (left @ Self::Z3(_), Self::Matrix(right)) => left / single_cell(right)?,
        }
    }
}

fn single_cell(mut matrix: Matrix<Z3Object>) -> Result<Z3Object, ToZ3Error> {
    if matrix.rows != 1 || matrix.cols != 1 || matrix.elements.len() != 1 {
        return Err(ToZ3Error::Shape(
            "matrix division is only supported for 1x1 matrices",
        ));
    }
    Ok(matrix.elements.pop().unwrap())
}

fn multiply_matrices(
    left: Matrix<Z3Object>,
    right: Matrix<Z3Object>,
) -> Result<Z3Object, ToZ3Error> {
    if left.cols != right.rows {
        return Err(ToZ3Error::Shape(
            "matrix multiplication requires compatible dimensions",
        ));
    }
    let capacity = left
        .rows
        .checked_mul(right.cols)
        .ok_or(ToZ3Error::DimensionOverflow)?;
    let mut elements = Vec::with_capacity(capacity);
    for row in 0..left.rows {
        for col in 0..right.cols {
            let mut terms = (0..left.cols).map(|inner| {
                left.elements[row * left.cols + inner].clone()
                    * right.elements[inner * right.cols + col].clone()
            });
            let first = terms.next().ok_or(ToZ3Error::Empty(
                "matrix dot product requires at least one term",
            ))??;
            elements.push(terms.try_fold(first, |sum, term| sum + term?)?);
        }
    }
    Ok(Z3Object::Matrix(Matrix {
        rows: left.rows,
        cols: right.cols,
        elements,
    }))
}

fn compare(left: Z3Object, comparison: Cmp, right: Z3Object) -> Result<Bool, ToZ3Error> {
    match (left, right) {
        (Z3Object::Z3(left), Z3Object::Z3(right)) => {
            if left.as_bool().is_some() || right.as_bool().is_some() {
                Err(ToZ3Error::InvalidOperands(
                    "boolean scalars cannot be compared",
                ))
            } else if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                Ok(compare_int(left, comparison, right))
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
        (Z3Object::Matrix(left), Z3Object::Matrix(right)) => {
            if !matches!(comparison, Cmp::Eq | Cmp::Ne) {
                return Err(ToZ3Error::InvalidOperands(
                    "matrix ordering comparisons are not supported",
                ));
            }
            if left.rows != right.rows || left.cols != right.cols {
                return Err(ToZ3Error::Shape(
                    "matrix equality requires equal dimensions",
                ));
            }
            let comparisons: Vec<_> = left
                .elements
                .into_iter()
                .zip(right.elements)
                .map(|(left, right)| compare(left, Cmp::Eq, right))
                .collect::<Result<_, _>>()?;
            let equality = Bool::and(&comparisons);
            if matches!(comparison, Cmp::Ne) {
                Ok(equality.not())
            } else {
                Ok(equality)
            }
        }
        (Z3Object::Matrix(_), Z3Object::Z3(_)) | (Z3Object::Z3(_), Z3Object::Matrix(_)) => Err(
            ToZ3Error::InvalidOperands("scalar-matrix comparisons are not supported"),
        ),
    }
}

fn compare_int(left: Int, comparison: Cmp, right: Int) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Ne => left.eq(right).not(),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
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

pub fn to_z3<Metadata>(γ: &Environment, e: &Expr<Metadata>) -> Result<Z3Object, ToZ3Error> {
    lower(γ, e)
}

fn lower<Metadata>(γ: &Environment, e: &Expr<Metadata>) -> Result<Z3Object, ToZ3Error> {
    match &e.raw {
        RawExpr::Hole => Err(ToZ3Error::Unsupported("holes are not supported by to_z3")),
        RawExpr::Type(_) => Err(ToZ3Error::Unsupported(
            "type expressions are not supported by to_z3",
        )),
        RawExpr::Variable(variable) => {
            let τ = γ
                .types
                .get(variable)
                .ok_or_else(|| ToZ3Error::MissingVariableType(variable.clone()))?;
            Ok(match τ {
                Type::Bool => Z3Object::Z3(Bool::new_const(variable.z3_name()).into()),
                Type::Nat | Type::Int => Z3Object::Z3(Int::new_const(variable.z3_name()).into()),
                Type::Real => Z3Object::Z3(Real::new_const(variable.z3_name()).into()),
                Type::Matrix(rows, cols) => {
                    let rows = usize::try_from(*rows).map_err(|_| ToZ3Error::DimensionOverflow)?;
                    let cols = usize::try_from(*cols).map_err(|_| ToZ3Error::DimensionOverflow)?;
                    let capacity = rows.checked_mul(cols).ok_or(ToZ3Error::DimensionOverflow)?;
                    let mut elements = Vec::with_capacity(capacity);
                    for row in 1..=rows {
                        for col in 1..=cols {
                            elements.push(Z3Object::Z3(
                                Real::new_const(format!("{}_{{{row},{col}}}", variable.z3_name()))
                                    .into(),
                            ));
                        }
                    }
                    Z3Object::Matrix(Matrix {
                        rows,
                        cols,
                        elements,
                    })
                }
            })
        }
        RawExpr::NatLiteral(value) => Ok(Z3Object::Z3(Int::from_u64(*value).into())),
        RawExpr::Monop(Monop::Neg, inner) => lower(γ, inner)?.neg(),
        RawExpr::Binop(Binop::Div, left, right) => lower(γ, left)? / lower(γ, right)?,
        RawExpr::Binop(Binop::Power, base, exponent) => {
            let exponent = γ
                .equalities
                .get(&exponent.without_metadata())
                .copied()
                .ok_or(ToZ3Error::MissingPowerExponent)?;
            lower_power(γ, base, exponent)
        }
        RawExpr::Binop(Binop::ElementOf, left, right) => lower_membership(γ, left, right),
        RawExpr::Finop(Finop::Plus, expressions) => {
            lower_finite(γ, expressions, Add::add, "addition")
        }
        RawExpr::Finop(Finop::Times, expressions) => {
            lower_finite(γ, expressions, Mul::mul, "multiplication")
        }
        RawExpr::Matrix(matrix) => {
            let expected_elements = matrix
                .rows
                .checked_mul(matrix.cols)
                .ok_or(ToZ3Error::DimensionOverflow)?;
            if matrix.elements.len() != expected_elements {
                return Err(ToZ3Error::InvalidMatrixLiteral);
            }
            Ok(Z3Object::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .iter()
                    .map(|expression| lower(γ, expression))
                    .collect::<Result<_, _>>()?,
            }))
        }
        RawExpr::CmpChain(chain) => lower_cmp_chain(γ, chain),
        RawExpr::LogicChain(_) => Err(ToZ3Error::Unsupported(
            "logic chains are not supported by to_z3",
        )),
        RawExpr::Monop(_, _)
        | RawExpr::Binop(_, _, _)
        | RawExpr::Triop(_, _, _, _)
        | RawExpr::Finop(_, _)
        | RawExpr::Seqop(_, _, _) => Err(ToZ3Error::Unsupported(
            "expression is not supported by to_z3",
        )),
    }
}

fn lower_membership<Metadata>(
    environment: &Environment,
    left: &Expr<Metadata>,
    right: &Expr<Metadata>,
) -> Result<Z3Object, ToZ3Error> {
    let (RawExpr::Variable(variable), RawExpr::Type(expected)) = (&left.raw, &right.raw) else {
        return Ok(Z3Object::Z3(Bool::from_bool(false).into()));
    };
    let Some(actual) = environment.types.get(variable) else {
        return Ok(Z3Object::Z3(Bool::from_bool(false).into()));
    };
    let result = match (actual, expected) {
        (Type::Bool, TypeExpr::Bool)
        | (Type::Int, TypeExpr::Int)
        | (Type::Real, TypeExpr::Real) => Bool::from_bool(true),
        (Type::Nat, TypeExpr::Nat) => Int::new_const(variable.z3_name()).ge(0),
        (Type::Matrix(rows, cols), TypeExpr::Matrix(expected_rows, expected_cols)) => {
            let row_symbol = Int::new_const(dimension_name(variable, "rows"));
            let col_symbol = Int::new_const(dimension_name(variable, "cols"));
            let expected_rows = lower_dimension(environment, expected_rows, "row")?;
            let expected_cols = lower_dimension(environment, expected_cols, "column")?;
            Bool::and(&[
                row_symbol.eq(Int::from_u64(*rows)),
                col_symbol.eq(Int::from_u64(*cols)),
                expected_rows.eq(&row_symbol),
                expected_cols.eq(&col_symbol),
            ])
        }
        _ => Bool::from_bool(false),
    };
    Ok(Z3Object::Z3(result.into()))
}

fn lower_dimension<Metadata>(
    environment: &Environment,
    expression: &Expr<Metadata>,
    axis: &str,
) -> Result<Int, ToZ3Error> {
    let Z3Object::Z3(expression) = lower(environment, expression)? else {
        return Err(ToZ3Error::InvalidOperands(match axis {
            "row" => "matrix row dimension must be a natural-number scalar",
            _ => "matrix column dimension must be a natural-number scalar",
        }));
    };
    expression
        .as_int()
        .ok_or(ToZ3Error::InvalidOperands(match axis {
            "row" => "matrix row dimension must be a natural-number scalar",
            _ => "matrix column dimension must be a natural-number scalar",
        }))
}

fn dimension_name(variable: &Variable, axis: &str) -> String {
    format!("{}_{{{axis}}}", variable.z3_name())
}

fn lower_cmp_chain<Metadata>(
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

fn lower_power<Metadata>(
    γ: &Environment,
    base: &Expr<Metadata>,
    exponent: u64,
) -> Result<Z3Object, ToZ3Error> {
    let lowered_base = lower(γ, base)?;
    if let Z3Object::Matrix(matrix) = &lowered_base
        && matrix.rows != matrix.cols
    {
        return Err(ToZ3Error::Shape("matrix power requires a square matrix"));
    }
    if exponent == 0 {
        return match lowered_base {
            Z3Object::Z3(expression) if expression.as_int().is_some() => {
                Ok(Z3Object::Z3(Int::from_u64(1).into()))
            }
            Z3Object::Z3(expression) if expression.as_real().is_some() => {
                Ok(Z3Object::Z3(Real::from_int(&Int::from_u64(1)).into()))
            }
            Z3Object::Z3(_) => Err(ToZ3Error::InvalidOperands(
                "zero power requires a numeric scalar base",
            )),
            Z3Object::Matrix(matrix) => Ok(Z3Object::Matrix(matrix_identity(&matrix)?)),
        };
    }

    (1..exponent).try_fold(lowered_base, |power, _| power * lower(γ, base)?)
}

fn matrix_identity(matrix: &Matrix<Z3Object>) -> Result<Matrix<Z3Object>, ToZ3Error> {
    let mut real = false;
    for element in &matrix.elements {
        match element {
            Z3Object::Z3(expression) if expression.as_int().is_some() => {}
            Z3Object::Z3(expression) if expression.as_real().is_some() => real = true,
            Z3Object::Z3(_) => {
                return Err(ToZ3Error::InvalidOperands(
                    "matrix identity requires numeric scalar cells",
                ));
            }
            Z3Object::Matrix(_) => {
                return Err(ToZ3Error::InvalidOperands(
                    "matrix identity does not support nested matrices",
                ));
            }
        }
    }
    let mut elements = Vec::with_capacity(
        matrix
            .rows
            .checked_mul(matrix.cols)
            .ok_or(ToZ3Error::DimensionOverflow)?,
    );
    for row in 0..matrix.rows {
        for col in 0..matrix.cols {
            let value = u64::from(row == col);
            if real {
                elements.push(Z3Object::Z3(Real::from_int(&Int::from_u64(value)).into()));
            } else {
                elements.push(Z3Object::Z3(Int::from_u64(value).into()));
            }
        }
    }
    Ok(Matrix {
        rows: matrix.rows,
        cols: matrix.cols,
        elements,
    })
}

fn lower_finite<Metadata>(
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
    use z3::{SatResult, Solver, SortKind, ast::Int};

    use crate::{
        Binop, Cmp, CmpChain, Expr, Finop, Matrix, Monop, RawExpr, Type, TypeExpr, Variable,
        to_z3::{Environment, ToZ3Error, Z3Object, to_z3 as lower_to_z3},
    };

    fn to_z3<Metadata>(environment: Environment, expression: Expr<Metadata>) -> Z3Object {
        lower_to_z3(&environment, &expression).unwrap()
    }

    fn assert_lowering_error<Metadata>(
        environment: Environment,
        expression: Expr<Metadata>,
        expected: ToZ3Error,
    ) {
        assert_eq!(lower_to_z3(&environment, &expression).err(), Some(expected));
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
    fn test_missing_variable_type_returns_an_error() {
        let variable = Variable::new("x");
        assert_lowering_error(
            Environment::default(),
            Expr::<()>::new(RawExpr::Variable(variable.clone())),
            ToZ3Error::MissingVariableType(variable),
        );
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
    fn test_incompatible_element_of_is_false() {
        let membership = Expr::<()>::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(Variable::new("x"))),
            Expr::new(RawExpr::Type(TypeExpr::Real)),
        ));
        assert_eq!(
            scalar(Environment::default(), membership).to_string(),
            "false"
        );
    }

    #[test]
    fn test_symbolic_matrix_membership_uses_concrete_environment_dimensions() {
        let a = Variable::new("A");
        let n = Variable::new("n");
        let d = Variable::new("d");
        let p = Variable::new("p");
        let environment = Environment {
            types: [
                (a.clone(), Type::Matrix(3, 8)),
                (n.clone(), Type::Nat),
                (d.clone(), Type::Nat),
                (p.clone(), Type::Nat),
            ]
            .into_iter()
            .collect(),
            equalities: Default::default(),
        };
        let variable = |variable| Expr::new(RawExpr::Variable(variable));
        let membership = Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            variable(a),
            Expr::new(RawExpr::Type(TypeExpr::Matrix(
                variable(n.clone()),
                Expr::new(RawExpr::Finop(
                    Finop::Plus,
                    vec![variable(d.clone()), variable(p.clone())],
                )),
            ))),
        ));
        let assertion = scalar(environment, membership).as_bool().unwrap();
        let solver = Solver::new();
        solver.assert(assertion);
        solver.push();
        solver.assert(Int::new_const(n.z3_name()).eq(3));
        solver.assert(Int::new_const(d.z3_name()).eq(4));
        solver.assert(Int::new_const(p.z3_name()).eq(4));
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop(1);
        solver.push();
        solver.assert(Int::new_const(n.z3_name()).eq(3));
        solver.assert(Int::new_const(d.z3_name()).eq(4));
        solver.assert(Int::new_const(p.z3_name()).eq(5));
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);
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
                exponent().without_metadata(),
            ))
        };
        let environment = |value| Environment {
            types: [(x.clone(), Type::Int)].into_iter().collect(),
            equalities: [(exponent().without_metadata(), value)]
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
            Environment::default(),
            power,
            ToZ3Error::MissingPowerExponent,
        );
    }

    #[test]
    fn test_matrix_variable_and_literal_lowering() {
        let a = Variable::new("A");
        let lowered = matrix(
            Environment {
                types: [(a.clone(), Type::Matrix(2, 2))].into_iter().collect(),
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
        assert_eq!(matrix_strings(&literal), vec!["1", "2"]);
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
        assert_eq!(matrix_strings(&integer_identity), vec!["1", "0", "0", "1"]);
    }

    #[test]
    fn test_positive_matrix_power_uses_matrix_multiplication() {
        let a = Variable::new("A");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        let squared = matrix(
            Environment {
                types: [(a.clone(), Type::Matrix(2, 2))].into_iter().collect(),
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
            equalities: HashMap::new(),
        };

        expect!["(not (and (= |A_{1,1}| |B_{1,1}|) (= |A_{1,2}| |B_{1,2}|)))"]
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
                    (a.clone(), Type::Matrix(1, 1)),
                    (b.clone(), Type::Matrix(1, 1)),
                ]
                .into_iter()
                .collect(),
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
                types: [(a.clone(), Type::Matrix(1, 1))].into_iter().collect(),
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
