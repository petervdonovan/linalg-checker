use std::{collections::HashMap, fmt::Display};

use crate::{Expr, Matrix, Type, Variable};

pub enum Z3Object {
    Matrix(Matrix<Z3Object>),
    Z3(z3::ast::Dynamic),
}

#[derive(Default)]
pub struct TypeEnvironment {
    pub types: HashMap<Variable, Type>,
}

pub fn to_z3<Metadata>(γ: TypeEnvironment, e: Expr<Metadata>) -> Z3Object {
    todo!()
}

impl Display for Z3Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z3Object::Matrix(matrix) => {
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
        for (name, r#type, expected_sort) in [
            ("b", Type::Bool, SortKind::Bool),
            ("n", Type::Nat, SortKind::Int),
            ("i", Type::Int, SortKind::Int),
            ("x", Type::Real, SortKind::Real),
        ] {
            let variable = Variable::new(name);
            let environment = TypeEnvironment {
                types: [(variable.clone(), r#type)].into_iter().collect(),
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
    fn test_division_and_power() {
        let quotient = MetaExpr::new(RawExpr::Binop(
            Binop::Div,
            MetaExpr::new(RawExpr::NatLiteral(8)),
            MetaExpr::new(RawExpr::NatLiteral(2)),
        ));
        let power = MetaExpr::new(RawExpr::Binop(
            Binop::Power,
            quotient,
            MetaExpr::new(RawExpr::NatLiteral(3)),
        ));

        expect!["(^ (div 8 2) 3)"]
            .assert_eq(&scalar(TypeEnvironment::default(), power).to_string());
    }
}
