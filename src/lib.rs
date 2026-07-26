#![allow(mixed_script_confusables)]

pub mod find_model;
pub mod from_tex;
pub mod normalize;
pub mod to_tex;
pub mod to_z3;

use std::{collections::HashMap, ops::Deref, rc::Rc};

pub enum Type {
    Bool,
    Nat,
    Int,
    Real,
    Matrix(u64, u64),
}

#[derive(Default)]
pub struct Environment {
    pub types: HashMap<Variable, Type>,
    pub equalities: HashMap<Expr<()>, u64>,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Variable {
    pub name: String,
    pub non_numeric_subscript: String,
    pub annotations: Vec<Annotation>,
}

impl Variable {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            non_numeric_subscript: String::new(),
            annotations: Vec::new(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Annotation {
    Hat,
    Tilde,
    Arrow,
    Prime,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cmp {
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Logic {
    Iff,
    Imp,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Monop {
    Trace,
    Det,
    Neg,
    Inverse,
    Norm1,
    Norm2,
    NormInfty,
    NormFrob,
    // Dim,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binop {
    // plus and times are associative, hence finops not binops
    Div,
    Power,
    // dotprod omitted
    InnerProd,
    // In,
    SingleSubscript,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Triop {
    DoubleSubscript,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Finop {
    // Span,
    Plus, // normalize by associativity
    Times,
    Max,
    Min,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum SeqOp {
    Sum,
    Prod,
}
#[derive(PartialEq, Eq, Hash)]
pub struct Expr<Metadata>(Rc<MetaExpr<Metadata>>);

impl<Metadata> Clone for Expr<Metadata> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<Metadata> Deref for Expr<Metadata> {
    type Target = MetaExpr<Metadata>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Metadata> Expr<Metadata> {
    pub fn with_metadata(meta: Metadata, raw: RawExpr<Metadata>) -> Self {
        Self(Rc::new(MetaExpr { meta, raw }))
    }

    pub fn get_mut(&mut self) -> Option<&mut MetaExpr<Metadata>> {
        Rc::get_mut(&mut self.0)
    }

    pub fn without_metadata(&self) -> Expr<()> {
        let raw = match &self.raw {
            RawExpr::Variable(variable) => RawExpr::Variable(variable.clone()),
            RawExpr::NatLiteral(value) => RawExpr::NatLiteral(*value),
            RawExpr::Matrix(matrix) => RawExpr::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix.elements.iter().map(Expr::without_metadata).collect(),
            }),
            RawExpr::Monop(op, expression) => RawExpr::Monop(*op, expression.without_metadata()),
            RawExpr::Binop(op, left, right) => {
                RawExpr::Binop(*op, left.without_metadata(), right.without_metadata())
            }
            RawExpr::Triop(op, first, second, third) => RawExpr::Triop(
                *op,
                first.without_metadata(),
                second.without_metadata(),
                third.without_metadata(),
            ),
            RawExpr::Finop(op, expressions) => RawExpr::Finop(
                *op,
                expressions.iter().map(Expr::without_metadata).collect(),
            ),
            RawExpr::CmpChain(chain) => RawExpr::CmpChain(CmpChain {
                start: chain.start.without_metadata(),
                assertions: chain
                    .assertions
                    .iter()
                    .map(|(op, expression)| (*op, expression.without_metadata()))
                    .collect(),
            }),
            RawExpr::LogicChain(chain) => RawExpr::LogicChain(LogicChain {
                start: chain.start.without_metadata(),
                assertions: chain
                    .assertions
                    .iter()
                    .map(|(op, expression)| (*op, expression.without_metadata()))
                    .collect(),
            }),
            RawExpr::Seqop(op, range, body) => RawExpr::Seqop(
                *op,
                SeqopRange {
                    index_variable: range.index_variable.clone(),
                    from: range.from.without_metadata(),
                    to: range.to.without_metadata(),
                },
                body.without_metadata(),
            ),
        };
        Expr::new(raw)
    }
}

impl<Metadata: Default> Expr<Metadata> {
    pub fn new(raw: RawExpr<Metadata>) -> Self {
        Self::with_metadata(Metadata::default(), raw)
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct MetaExpr<Metadata> {
    pub meta: Metadata,
    pub raw: RawExpr<Metadata>,
}
#[derive(PartialEq, Eq, Hash)]
pub struct SeqopRange<Metadata> {
    pub index_variable: Variable,
    pub from: Expr<Metadata>,
    pub to: Expr<Metadata>,
}
#[derive(PartialEq, Eq, Hash)]
pub struct CmpChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Cmp, Expr<Metadata>)>,
}
#[derive(PartialEq, Eq, Hash)]
pub struct LogicChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Logic, Expr<Metadata>)>,
}
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Matrix<Cell> {
    pub rows: usize,
    pub cols: usize,
    pub elements: Vec<Cell>,
}
impl<Cell: Clone> Matrix<Cell> {
    fn at(&self, i: usize, j: usize) -> Cell {
        self.elements[i * self.cols + j].clone()
    }
}
impl<Cell> std::ops::Mul<Matrix<Cell>> for Matrix<Cell>
where
    Cell: std::ops::Mul<Cell, Output = Cell> + std::iter::Sum<Cell> + Clone,
{
    type Output = Matrix<Cell>;

    fn mul(self, rhs: Matrix<Cell>) -> Self::Output {
        let rows = self.rows;
        let cols = rhs.cols;
        let mut elements = Vec::new();
        assert!(
            self.cols == rhs.rows,
            "matrix multiplication requires compatible dimensions"
        );
        for i in 0..rows {
            for j in 0..cols {
                elements.push((0..self.cols).map(|k| self.at(i, k) * rhs.at(k, j)).sum());
            }
        }
        Matrix {
            rows,
            cols,
            elements,
        }
    }
}
#[derive(PartialEq, Eq, Hash)]
pub enum RawExpr<Metadata> {
    Variable(Variable),
    NatLiteral(u64),
    Matrix(Matrix<Expr<Metadata>>),
    Monop(Monop, Expr<Metadata>),
    Binop(Binop, Expr<Metadata>, Expr<Metadata>),
    Triop(Triop, Expr<Metadata>, Expr<Metadata>, Expr<Metadata>),
    Finop(Finop, Vec<Expr<Metadata>>),
    CmpChain(CmpChain<Metadata>),
    LogicChain(LogicChain<Metadata>),
    Seqop(SeqOp, SeqopRange<Metadata>, Expr<Metadata>),
}

#[cfg(test)]
mod tests {
    use super::{Expr, Finop, RawExpr, Variable};

    struct MetadataWithoutClone;

    #[test]
    fn cloning_expr_does_not_require_cloneable_metadata() {
        let expression = Expr::with_metadata(MetadataWithoutClone, RawExpr::NatLiteral(1));
        let _clone = expression.clone();
    }

    #[test]
    fn without_metadata_recursively_erases_metadata() {
        fn expression(metadata: u8) -> Expr<u8> {
            Expr::with_metadata(
                metadata,
                RawExpr::Finop(
                    Finop::Plus,
                    vec![
                        Expr::with_metadata(metadata, RawExpr::Variable(Variable::new("x"))),
                        Expr::with_metadata(
                            metadata,
                            RawExpr::Finop(
                                Finop::Times,
                                vec![
                                    Expr::with_metadata(metadata, RawExpr::NatLiteral(2)),
                                    Expr::with_metadata(metadata, RawExpr::NatLiteral(3)),
                                ],
                            ),
                        ),
                    ],
                ),
            )
        }

        assert!(expression(1).without_metadata() == expression(2).without_metadata());
    }
}
