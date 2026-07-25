#![allow(mixed_script_confusables)]

pub mod from_tex;
pub mod normalize;
pub mod to_tex;
pub mod to_z3;

use std::rc::Rc;

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

pub enum Cmp {
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
}
pub enum Logic {
    Iff,
    Imp,
}

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

pub enum Binop {
    // plus and times are associative, hence finops not binops
    Div,
    Power,
    // dotprod omitted
    InnerProd,
    // In,
    SingleSubscript,
}

pub enum Triop {
    DoubleSubscript,
}

pub enum Finop {
    // Span,
    Plus, // normalize by associativity
    Times,
    Max,
    Min,
}

pub enum SeqOp {
    Sum,
    Prod,
}

type Expr<Metadata> = Rc<MetaExpr<Metadata>>;

pub struct MetaExpr<Metadata> {
    pub meta: Metadata,
    pub raw: RawExpr<Metadata>,
}

impl<Metadata: Default> MetaExpr<Metadata> {
    pub fn new(raw: RawExpr<Metadata>) -> Rc<Self> {
        Rc::new(Self {
            meta: Metadata::default(),
            raw,
        })
    }
}

pub struct SeqopRange<Metadata> {
    pub index_variable: Variable,
    pub from: Expr<Metadata>,
    pub to: Expr<Metadata>,
}
pub struct CmpChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Cmp, Expr<Metadata>)>,
}
pub struct LogicChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Logic, Expr<Metadata>)>,
}
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
