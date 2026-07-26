use std::{
    collections::HashMap,
    fmt::Display,
    ops::{Add, Div, Mul, Neg},
};

use z3::ast::{Bool, Int, Real};

use crate::{Binop, Expr, Finop, Matrix, Monop, RawExpr, Type, Variable};

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
            Self::Matrix(_) => panic!("matrix negation is not supported"),
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
            (Self::Matrix(_), Self::Matrix(_)) => panic!("matrix addition is not supported"),
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
            (Self::Matrix(_), Self::Matrix(_)) => {
                panic!("matrix multiplication is not supported")
            }
            (Self::Matrix(_), Self::Z3(_)) | (Self::Z3(_), Self::Matrix(_)) => {
                panic!("scalar-matrix multiplication is not supported")
            }
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
            (Self::Matrix(_), Self::Matrix(_)) => panic!("matrix division is not supported"),
            (Self::Matrix(_), Self::Z3(_)) | (Self::Z3(_), Self::Matrix(_)) => {
                panic!("scalar-matrix division is not supported")
            }
        }
    }
}

#[derive(Default)]
pub struct TypeEnvironment {
    pub types: HashMap<Variable, Type>,
}

pub fn to_z3<Metadata>(γ: TypeEnvironment, e: Expr<Metadata>) -> Z3Object {
    lower(&γ, &e)
}

fn lower<Metadata>(γ: &TypeEnvironment, e: &Expr<Metadata>) -> Z3Object {
    match &e.raw {
        RawExpr::Variable(variable) => {
            let τ = γ
                .types
                .get(variable)
                .unwrap_or_else(|| panic!("variable is missing from the type environment"));
            let expression = match τ {
                Type::Bool => Bool::new_const(variable.name.clone()).into(),
                Type::Nat | Type::Int => Int::new_const(variable.name.clone()).into(),
                Type::Real => Real::new_const(variable.name.clone()).into(),
                Type::Matrix => panic!("matrix variables are not supported"),
            };
            Z3Object::Z3(expression)
        }
        RawExpr::NatLiteral(value) => Z3Object::Z3(Int::from_u64(*value).into()),
        RawExpr::Monop(Monop::Neg, inner) => -lower(γ, inner),
        RawExpr::Binop(Binop::Div, left, right) => lower(γ, left) / lower(γ, right),
        RawExpr::Finop(Finop::Plus, expressions) => {
            lower_finite(γ, expressions, Add::add, "addition")
        }
        RawExpr::Finop(Finop::Times, expressions) => {
            lower_finite(γ, expressions, Mul::mul, "multiplication")
        }
        RawExpr::Matrix(_) => panic!("matrix expressions are not supported"),
        RawExpr::CmpChain(_) | RawExpr::LogicChain(_) => {
            panic!("comparison and logic chains are not supported")
        }
        RawExpr::Monop(_, _)
        | RawExpr::Binop(_, _, _)
        | RawExpr::Triop(_, _, _, _)
        | RawExpr::Finop(_, _)
        | RawExpr::Seqop(_, _, _) => panic!("expression is not supported by to_z3"),
    }
}

fn lower_finite<Metadata>(
    γ: &TypeEnvironment,
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
    use expect_test::expect;
    use z3::SortKind;

    use crate::{
        Binop, Expr, Finop, MetaExpr, Monop, RawExpr, Type, Variable,
        to_z3::{TypeEnvironment, Z3Object, to_z3},
    };

    fn scalar(environment: TypeEnvironment, expression: Expr<()>) -> z3::ast::Dynamic {
        match to_z3(environment, expression) {
            Z3Object::Z3(expression) => expression,
            Z3Object::Matrix(_) => panic!("expected a scalar Z3 expression"),
        }
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
            let environment = TypeEnvironment {
                types: [(variable.clone(), τ)].into_iter().collect(),
            };

            assert_eq!(
                scalar(environment, MetaExpr::new(RawExpr::Variable(variable))).sort_kind(),
                expected_sort,
            );
        }
    }

    #[test]
    fn test_natural_literal() {
        expect!["42"].assert_eq(
            &scalar(
                TypeEnvironment::default(),
                MetaExpr::new(RawExpr::NatLiteral(42)),
            )
            .to_string(),
        );
    }

    #[test]
    fn test_negation() {
        expect!["(- 7)"].assert_eq(
            &scalar(
                TypeEnvironment::default(),
                MetaExpr::new(RawExpr::Monop(
                    Monop::Neg,
                    MetaExpr::new(RawExpr::NatLiteral(7)),
                )),
            )
            .to_string(),
        );
    }

    #[test]
    fn test_addition_and_multiplication() {
        let product = MetaExpr::new(RawExpr::Finop(
            Finop::Times,
            vec![
                MetaExpr::new(RawExpr::NatLiteral(3)),
                MetaExpr::new(RawExpr::NatLiteral(4)),
            ],
        ));
        let sum = MetaExpr::new(RawExpr::Finop(
            Finop::Plus,
            vec![MetaExpr::new(RawExpr::NatLiteral(2)), product],
        ));

        expect!["(+ 2 (* 3 4))"].assert_eq(&scalar(TypeEnvironment::default(), sum).to_string());
    }

    #[test]
    fn test_division() {
        let quotient = MetaExpr::new(RawExpr::Binop(
            Binop::Div,
            MetaExpr::new(RawExpr::NatLiteral(8)),
            MetaExpr::new(RawExpr::NatLiteral(2)),
        ));

        expect!["(div 8 2)"].assert_eq(&scalar(TypeEnvironment::default(), quotient).to_string());
    }

    #[test]
    fn test_mixed_numeric_operations_promote_to_real() {
        let x = Variable::new("x");
        let environment = || TypeEnvironment {
            types: [(x.clone(), Type::Real)].into_iter().collect(),
        };
        let real = || MetaExpr::new(RawExpr::Variable(x.clone()));
        let integer = || MetaExpr::new(RawExpr::NatLiteral(2));

        let addition = MetaExpr::new(RawExpr::Finop(Finop::Plus, vec![real(), integer()]));
        let multiplication = MetaExpr::new(RawExpr::Finop(Finop::Times, vec![integer(), real()]));
        let division = MetaExpr::new(RawExpr::Binop(Binop::Div, real(), integer()));

        expect!["(+ x (to_real 2))"].assert_eq(&scalar(environment(), addition).to_string());
        expect!["(* (to_real 2) x)"].assert_eq(&scalar(environment(), multiplication).to_string());
        expect!["(/ x (to_real 2))"].assert_eq(&scalar(environment(), division).to_string());
    }
}
