#![allow(mixed_script_confusables)]

pub mod from_tex;
pub mod normalize;
pub mod to_tex;
pub mod to_z3;

use std::{ops::Deref, rc::Rc};

pub enum Type {
    Bool,
    Nat,
    Int,
    Real,
    Matrix,
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
#[derive(PartialEq, Eq, Hash)]
pub enum Cmp {
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
}
#[derive(PartialEq, Eq, Hash)]
pub enum Logic {
    Iff,
    Imp,
}
#[derive(PartialEq, Eq, Hash)]
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
#[derive(PartialEq, Eq, Hash)]
pub enum Binop {
    // plus and times are associative, hence finops not binops
    Div,
    Power,
    // dotprod omitted
    InnerProd,
    // In,
    SingleSubscript,
}
#[derive(PartialEq, Eq, Hash)]
pub enum Triop {
    DoubleSubscript,
}
#[derive(PartialEq, Eq, Hash)]
pub enum Finop {
    // Span,
    Plus, // normalize by associativity
    Times,
    Max,
    Min,
}
#[derive(PartialEq, Eq, Hash)]
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
        todo!()
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
#[derive(PartialEq, Eq, Hash)]
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
        assert!(self.cols == rhs.rows);
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
    use super::{Expr, RawExpr};

    struct MetadataWithoutClone;

    #[test]
    fn cloning_expr_does_not_require_cloneable_metadata() {
        let expression = Expr::with_metadata(MetadataWithoutClone, RawExpr::NatLiteral(1));
        let _clone = expression.clone();
    }
}
