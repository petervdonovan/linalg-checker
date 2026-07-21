pub mod to_tex;
pub mod from_tex;

use std::rc::Rc;

pub struct Variable {
    pub name: String,
    pub non_numeric_subscript: String,
    pub annotations: Vec<Annotation>
}

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
    Plus,  // normalize by associativity
    Times,
    Max,
    Min,
    LogicChain,
    CmpChain,
}

pub enum SeqOp {
    Sum,
    Prod,
}

type Expr<Metadata> = Rc<MetaExpr<Metadata>>;

pub struct MetaExpr<Metadata> {
    pub meta: Metadata,
    pub raw: RawExpr<Metadata>
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
pub enum RawExpr<Metadata> {
    Variable(Variable),
    Monop(Monop, Expr<Metadata>),
    Binop(Binop, Expr<Metadata>, Expr<Metadata>),
    Triop(Triop, Expr<Metadata>, Expr<Metadata>, Expr<Metadata>),
    Finop(Finop, Vec<Expr<Metadata>>),
    Seqop(Finop, SeqopRange<Metadata>, Expr<Metadata>),
}
