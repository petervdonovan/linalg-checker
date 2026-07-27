use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, Div, Mul, Neg},
};

use z3::{
    Solver,
    ast::{Bool, Int, Real},
};

use crate::{Binop, Cmp, CmpChain, Environment, Expr, Finop, Matrix, Model, Monop, RawExpr, Type};

impl Environment {
    pub fn models(&self, solver: &Solver) -> impl std::iter::Iterator<Item = Model> {
        std::iter::empty::<Model>() // todo: return a sequence of equalities between variables in the environment and expressions
    }
}

#[derive(Clone)]
pub enum Z3Object {
    Matrix(Matrix<Z3Object>),
    Z3(z3::ast::Dynamic),
}

impl Neg for Z3Object {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Self::Z3(expression) => {
                if let Some(expression) = expression.as_int() {
                    Self::Z3((-expression).into())
                } else if let Some(expression) = expression.as_real() {
                    Self::Z3((-expression).into())
                } else {
                    panic!("negation requires a numeric scalar")
                }
            }
            Self::Matrix(matrix) => Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix.elements.into_iter().map(Neg::neg).collect(),
            }),
        }
    }
}

impl Add for Z3Object {
    type Output = Self;

    fn add(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Self::Z3((left + right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Self::Z3((left + right).into())
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Self::Z3((Real::from_int(&left) + right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Self::Z3((left + Real::from_int(&right)).into())
                } else {
                    panic!("addition requires numeric scalars")
                }
            }
            (Self::Matrix(left), Self::Matrix(right)) => {
                assert!(
                    left.rows == right.rows && left.cols == right.cols,
                    "matrix addition requires equal dimensions"
                );
                Self::Matrix(Matrix {
                    rows: left.rows,
                    cols: left.cols,
                    elements: left
                        .elements
                        .into_iter()
                        .zip(right.elements)
                        .map(|(left, right)| left + right)
                        .collect(),
                })
            }
            (Self::Matrix(_), Self::Z3(_)) | (Self::Z3(_), Self::Matrix(_)) => {
                panic!("scalar-matrix addition is not supported")
            }
        }
    }
}

impl Mul for Z3Object {
    type Output = Self;

    fn mul(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Self::Z3((left * right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Self::Z3((left * right).into())
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Self::Z3((Real::from_int(&left) * right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Self::Z3((left * Real::from_int(&right)).into())
                } else {
                    panic!("multiplication requires numeric scalars")
                }
            }
            (Self::Matrix(left), Self::Matrix(right)) => Self::Matrix(left * right),
            (Self::Matrix(matrix), scalar @ Self::Z3(_)) => Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|element| element * scalar.clone())
                    .collect(),
            }),
            (scalar @ Self::Z3(_), Self::Matrix(matrix)) => Self::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|element| scalar.clone() * element)
                    .collect(),
            }),
        }
    }
}

impl Div for Z3Object {
    type Output = Self;

    fn div(self, right: Self) -> Self::Output {
        match (self, right) {
            (Self::Z3(left), Self::Z3(right)) => {
                if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                    Self::Z3((left / right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                    Self::Z3((left / right).into())
                } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                    Self::Z3((Real::from_int(&left) / right).into())
                } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                    Self::Z3((left / Real::from_int(&right)).into())
                } else {
                    panic!("division requires numeric scalars")
                }
            }
            (Self::Matrix(left), Self::Matrix(right)) => single_cell(left) / single_cell(right),
            (Self::Matrix(left), right @ Self::Z3(_)) => single_cell(left) / right,
            (left @ Self::Z3(_), Self::Matrix(right)) => left / single_cell(right),
        }
    }
}

impl Sum for Z3Object {
    fn sum<I: Iterator<Item = Self>>(mut iter: I) -> Self {
        let first = iter
            .next()
            .unwrap_or_else(|| panic!("matrix dot product requires at least one term"));
        iter.fold(first, Add::add)
    }
}

fn single_cell(mut matrix: Matrix<Z3Object>) -> Z3Object {
    assert!(
        matrix.rows == 1 && matrix.cols == 1 && matrix.elements.len() == 1,
        "matrix division is only supported for 1x1 matrices"
    );
    matrix.elements.pop().unwrap()
}

fn compare(left: Z3Object, comparison: Cmp, right: Z3Object) -> Bool {
    match (left, right) {
        (Z3Object::Z3(left), Z3Object::Z3(right)) => {
            if left.as_bool().is_some() || right.as_bool().is_some() {
                panic!("boolean scalars cannot be compared")
            } else if let (Some(left), Some(right)) = (left.as_int(), right.as_int()) {
                compare_int(left, comparison, right)
            } else if let (Some(left), Some(right)) = (left.as_real(), right.as_real()) {
                compare_real(left, comparison, right)
            } else if let (Some(left), Some(right)) = (left.as_int(), right.as_real()) {
                compare_real(Real::from_int(&left), comparison, right)
            } else if let (Some(left), Some(right)) = (left.as_real(), right.as_int()) {
                compare_real(left, comparison, Real::from_int(&right))
            } else {
                panic!("comparison requires numeric scalars")
            }
        }
        (Z3Object::Matrix(left), Z3Object::Matrix(right)) => {
            assert!(
                matches!(comparison, Cmp::Eq),
                "matrix ordering comparisons are not supported"
            );
            assert!(
                left.rows == right.rows && left.cols == right.cols,
                "matrix equality requires equal dimensions"
            );
            let comparisons: Vec<_> = left
                .elements
                .into_iter()
                .zip(right.elements)
                .map(|(left, right)| compare(left, Cmp::Eq, right))
                .collect();
            Bool::and(&comparisons)
        }
        (Z3Object::Matrix(_), Z3Object::Z3(_)) | (Z3Object::Z3(_), Z3Object::Matrix(_)) => {
            panic!("scalar-matrix comparisons are not supported")
        }
    }
}

fn compare_int(left: Int, comparison: Cmp, right: Int) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
    }
}

fn compare_real(left: Real, comparison: Cmp, right: Real) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
    }
}

pub fn to_z3<Metadata>(γ: Environment, e: Expr<Metadata>) -> Z3Object {
    lower(&γ, &e)
}

fn lower<Metadata>(γ: &Environment, e: &Expr<Metadata>) -> Z3Object {
    match &e.raw {
        RawExpr::Type(_) => panic!("type expressions are not supported by to_z3"),
        RawExpr::Variable(variable) => {
            let τ = γ
                .types
                .get(variable)
                .unwrap_or_else(|| panic!("variable is missing from the type environment"));
            match τ {
                Type::Bool => Z3Object::Z3(Bool::new_const(variable.name.clone()).into()),
                Type::Nat | Type::Int => Z3Object::Z3(Int::new_const(variable.name.clone()).into()),
                Type::Real => Z3Object::Z3(Real::new_const(variable.name.clone()).into()),
                Type::Matrix(rows, cols) => {
                    let rows =
                        usize::try_from(*rows).expect("matrix row count does not fit in usize");
                    let cols =
                        usize::try_from(*cols).expect("matrix column count does not fit in usize");
                    let capacity = rows
                        .checked_mul(cols)
                        .expect("matrix dimensions overflow usize");
                    let mut elements = Vec::with_capacity(capacity);
                    for row in 1..=rows {
                        for col in 1..=cols {
                            elements.push(Z3Object::Z3(
                                Real::new_const(format!("{}_{{{row},{col}}}", variable.name))
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
            }
        }
        RawExpr::NatLiteral(value) => Z3Object::Z3(Int::from_u64(*value).into()),
        RawExpr::Monop(Monop::Neg, inner) => -lower(γ, inner),
        RawExpr::Binop(Binop::Div, left, right) => lower(γ, left) / lower(γ, right),
        RawExpr::Binop(Binop::Power, base, exponent) => {
            let exponent = γ
                .equalities
                .get(&exponent.without_metadata())
                .copied()
                .unwrap_or_else(|| {
                    panic!("power exponent is missing from the equality environment")
                });
            lower_power(γ, base, exponent)
        }
        RawExpr::Binop(Binop::ElementOf, _, _) => {
            panic!("element-of expressions are not supported by to_z3")
        }
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
                .expect("matrix dimensions overflow usize");
            assert!(
                matrix.elements.len() == expected_elements,
                "matrix element count does not match its dimensions"
            );
            Z3Object::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .iter()
                    .map(|expression| lower(γ, expression))
                    .collect(),
            })
        }
        RawExpr::CmpChain(chain) => lower_cmp_chain(γ, chain),
        RawExpr::LogicChain(_) => panic!("logic chains are not supported"),
        RawExpr::Monop(_, _)
        | RawExpr::Binop(_, _, _)
        | RawExpr::Triop(_, _, _, _)
        | RawExpr::Finop(_, _)
        | RawExpr::Seqop(_, _, _) => panic!("expression is not supported by to_z3"),
    }
}

fn lower_cmp_chain<Metadata>(γ: &Environment, chain: &CmpChain<Metadata>) -> Z3Object {
    assert!(
        !chain.assertions.is_empty(),
        "comparison chain requires at least one assertion"
    );
    let mut previous = lower(γ, &chain.start);
    let mut comparisons = Vec::with_capacity(chain.assertions.len());
    for (comparison, current) in &chain.assertions {
        let current = lower(γ, current);
        comparisons.push(compare(previous, *comparison, current.clone()));
        previous = current;
    }
    let result = if comparisons.len() == 1 {
        comparisons.pop().unwrap()
    } else {
        Bool::and(&comparisons)
    };
    Z3Object::Z3(result.into())
}

fn lower_power<Metadata>(γ: &Environment, base: &Expr<Metadata>, exponent: u64) -> Z3Object {
    let lowered_base = lower(γ, base);
    if let Z3Object::Matrix(matrix) = &lowered_base {
        assert!(
            matrix.rows == matrix.cols,
            "matrix power requires a square matrix"
        );
    }
    if exponent == 0 {
        return match lowered_base {
            Z3Object::Z3(expression) if expression.as_int().is_some() => {
                Z3Object::Z3(Int::from_u64(1).into())
            }
            Z3Object::Z3(expression) if expression.as_real().is_some() => {
                Z3Object::Z3(Real::from_int(&Int::from_u64(1)).into())
            }
            Z3Object::Z3(_) => panic!("zero power requires a numeric scalar base"),
            Z3Object::Matrix(matrix) => Z3Object::Matrix(matrix_identity(&matrix)),
        };
    }

    (1..exponent).fold(lowered_base, |power, _| power * lower(γ, base))
}

fn matrix_identity(matrix: &Matrix<Z3Object>) -> Matrix<Z3Object> {
    let real = matrix.elements.iter().any(|element| match element {
        Z3Object::Z3(expression) if expression.as_int().is_some() => false,
        Z3Object::Z3(expression) if expression.as_real().is_some() => true,
        Z3Object::Z3(_) => panic!("matrix identity requires numeric scalar cells"),
        Z3Object::Matrix(_) => panic!("matrix identity does not support nested matrices"),
    });
    let mut elements = Vec::with_capacity(
        matrix
            .rows
            .checked_mul(matrix.cols)
            .expect("matrix dimensions overflow usize"),
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
    Matrix {
        rows: matrix.rows,
        cols: matrix.cols,
        elements,
    }
}

fn lower_finite<Metadata>(
    γ: &Environment,
    expressions: &[Expr<Metadata>],
    operation: fn(Z3Object, Z3Object) -> Z3Object,
    name: &str,
) -> Z3Object {
    let mut expressions = expressions.iter().map(|expression| lower(γ, expression));
    let first = expressions
        .next()
        .unwrap_or_else(|| panic!("{name} requires at least one operand"));
    expressions.fold(first, operation)
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
    use z3::SortKind;

    use crate::{
        Binop, Cmp, CmpChain, Expr, Finop, Matrix, Monop, RawExpr, Type, Variable,
        to_z3::{Environment, Z3Object, to_z3},
    };

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
    #[should_panic(expected = "type expressions are not supported by to_z3")]
    fn test_type_expression_is_not_lowered() {
        to_z3(
            Environment::default(),
            Expr::<()>::new(RawExpr::Type(Type::Real)),
        );
    }

    #[test]
    #[should_panic(expected = "element-of expressions are not supported by to_z3")]
    fn test_element_of_is_not_lowered() {
        to_z3(
            Environment::default(),
            Expr::<()>::new(RawExpr::Binop(
                Binop::ElementOf,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
                Expr::new(RawExpr::Type(Type::Real)),
            )),
        );
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
    #[should_panic(expected = "power exponent is missing from the equality environment")]
    fn test_power_requires_known_exponent_equality() {
        let power: Expr<()> = Expr::new(RawExpr::Binop(
            Binop::Power,
            Expr::new(RawExpr::NatLiteral(2)),
            Expr::new(RawExpr::Variable(Variable::new("n"))),
        ));

        to_z3(Environment::default(), power);
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
    #[should_panic(expected = "matrix power requires a square matrix")]
    fn test_non_square_matrix_power_panics() {
        let a = Variable::new("A");
        let exponent = Expr::new(RawExpr::Variable(Variable::new("n")));
        to_z3(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 2))].into_iter().collect(),
                equalities: [(exponent.clone(), 1)].into_iter().collect(),
            },
            Expr::new(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Variable(a)),
                exponent,
            )),
        );
    }

    #[test]
    #[should_panic(expected = "matrix multiplication requires compatible dimensions")]
    fn test_invalid_matrix_multiplication_panics() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        let product: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Times,
            vec![
                Expr::new(RawExpr::Variable(a.clone())),
                Expr::new(RawExpr::Variable(b.clone())),
            ],
        ));
        to_z3(
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
        );
    }

    #[test]
    #[should_panic(expected = "matrix addition requires equal dimensions")]
    fn test_mismatched_matrix_addition_panics() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        to_z3(
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
        );
    }

    #[test]
    #[should_panic(expected = "matrix division is only supported for 1x1 matrices")]
    fn test_larger_matrix_division_panics() {
        let a = Variable::new("A");
        to_z3(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 2))].into_iter().collect(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::Binop(
                Binop::Div,
                Expr::new(RawExpr::Variable(a)),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
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
    #[should_panic(expected = "boolean scalars cannot be compared")]
    fn test_boolean_comparison_panics() {
        let p = Variable::new("P");
        let q = Variable::new("Q");
        to_z3(
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
        );
    }

    #[test]
    #[should_panic(expected = "matrix equality requires equal dimensions")]
    fn test_mismatched_matrix_equality_panics() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        to_z3(
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
        );
    }

    #[test]
    #[should_panic(expected = "matrix ordering comparisons are not supported")]
    fn test_matrix_ordering_panics() {
        let a = Variable::new("A");
        let b = Variable::new("B");
        to_z3(
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
        );
    }

    #[test]
    #[should_panic(expected = "scalar-matrix comparisons are not supported")]
    fn test_scalar_matrix_comparison_panics() {
        let a = Variable::new("A");
        to_z3(
            Environment {
                types: [(a.clone(), Type::Matrix(1, 1))].into_iter().collect(),
                equalities: HashMap::new(),
            },
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::NatLiteral(1)),
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::Variable(a)))],
            })),
        );
    }

    #[test]
    #[should_panic(expected = "comparison chain requires at least one assertion")]
    fn test_empty_comparison_chain_panics() {
        to_z3(
            Environment::default(),
            Expr::<()>::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::NatLiteral(1)),
                assertions: vec![],
            })),
        );
    }
}
