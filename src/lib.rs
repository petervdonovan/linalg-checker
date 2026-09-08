#![allow(mixed_script_confusables)]

mod deep_clone;
pub mod elaboration;
pub mod enumerable_envspec;
pub mod find_model;
pub mod find_model_given_environment;
mod formula;
pub mod from_tex;
pub mod logic_lowering;
mod model_finding;
pub mod operator_visitors;
pub mod preprocessing;
pub mod to_tex;
pub mod to_z3;
mod type_expr;
pub mod type_resolver;
mod unification;
pub mod validate_argument;
pub mod visit;
pub mod visit_mut;
mod z3_utils;

use std::{
    collections::HashMap,
    error::Error,
    fmt,
    ops::Deref,
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_IMPLICIT_DIMENSION: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ImplicitDimension(u64);

impl ImplicitDimension {
    pub fn fresh() -> Self {
        Self(NEXT_IMPLICIT_DIMENSION.fetch_add(1, Ordering::Relaxed))
    }

    pub(crate) fn z3_name(self) -> String {
        format!("__implicit_dimension_{}", self.0)
    }

    pub(crate) fn nonce_id(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeBruijnIndex(usize);

impl DeBruijnIndex {
    pub(crate) const fn new(index: usize) -> Self {
        Self(index)
    }

    pub(crate) const fn get(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NaturalParameter {
    Variable(Variable),
    ImplicitDimension(ImplicitDimension),
}

impl NaturalParameter {
    pub(crate) fn z3_name(&self) -> String {
        match self {
            Self::Variable(variable) => variable.z3_name(),
            Self::ImplicitDimension(dimension) => dimension.z3_name(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NaturalEvaluationError {
    MissingAssignment(NaturalParameter),
    UnsupportedSyntax(&'static str),
    EmptyOperation(&'static str),
    NotANumeral,
    Overflow,
    UnboundNatural(DeBruijnIndex),
}

impl fmt::Display for NaturalEvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingAssignment(parameter) => {
                write!(f, "missing natural assignment for {parameter:?}")
            }
            Self::UnsupportedSyntax(message) => f.write_str(message),
            Self::EmptyOperation(operation) => {
                write!(f, "natural {operation} cannot be empty")
            }
            Self::NotANumeral => f.write_str("natural expression did not simplify to a numeral"),
            Self::Overflow => f.write_str("natural expression is outside the u64 range"),
            Self::UnboundNatural(index) => {
                write!(
                    f,
                    "unbound natural type index at de Bruijn index #{}",
                    index.get()
                )
            }
        }
    }
}

impl Error for NaturalEvaluationError {}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum TypeExpr<Metadata> {
    Bool,
    Nat,
    Int,
    Real,
    Matrix(Expr<Metadata>, Expr<Metadata>),
    Seq(Expr<Metadata>, Expr<Metadata>),
}

impl<Metadata> TypeExpr<Metadata> {
    pub fn with_default_metadata<NewMetadata: Default>(&self) -> TypeExpr<NewMetadata> {
        match self {
            Self::Bool => TypeExpr::Bool,
            Self::Nat => TypeExpr::Nat,
            Self::Int => TypeExpr::Int,
            Self::Real => TypeExpr::Real,
            Self::Matrix(rows, cols) => {
                TypeExpr::Matrix(rows.with_default_metadata(), cols.with_default_metadata())
            }
            Self::Seq(element, size) => TypeExpr::Seq(
                element.with_default_metadata(),
                size.with_default_metadata(),
            ),
        }
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct Environment {
    pub natural_assignment: HashMap<NaturalParameter, u64>,
}

impl Environment {
    pub fn evaluate_natural<Metadata>(
        &self,
        expression: &Expr<Metadata>,
    ) -> Result<u64, NaturalEvaluationError> {
        crate::z3_utils::evaluate_natural(expression, &self.natural_assignment)
    }

    pub(crate) fn evaluate_natural_with_context<Metadata>(
        &self,
        expression: &Expr<Metadata>,
        lexical_range_values: &[(Variable, u64)],
        bound_natural_values: &[u64],
    ) -> Result<u64, NaturalEvaluationError> {
        crate::z3_utils::evaluate_natural_with_context(
            expression,
            &self.natural_assignment,
            lexical_range_values,
            bound_natural_values,
        )
    }
}

pub type Model = Vec<Expr<()>>;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
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

    pub fn z3_name(&self) -> String {
        let mut name = self.name.clone();
        for annotation in &self.annotations {
            name = match annotation {
                Annotation::Hat => format!(r"\hat{{{name}}}"),
                Annotation::Tilde => format!(r"\tilde{{{name}}}"),
                Annotation::Arrow => format!(r"\vec{{{name}}}"),
                Annotation::Prime => name,
            };
        }
        if !self.non_numeric_subscript.is_empty() {
            name = format!("{name}_{{{}}}", self.non_numeric_subscript);
        }
        for annotation in &self.annotations {
            if matches!(annotation, Annotation::Prime) {
                name.push_str(r"^{\prime}");
            }
        }
        name
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Annotation {
    Hat,
    Tilde,
    Arrow,
    Prime,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Cmp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Logic {
    Iff,
    Imp,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Monop {
    Trace,
    Det,
    Diag,
    Neg,
    Inverse,
    Norm1,
    Norm2,
    NormInfty,
    NormFrob,
    Transpose,
    // Dim,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Binop {
    // plus and times are associative, hence finops not binops
    Div,
    Power,
    // dotprod omitted
    InnerProd,
    Cast,
    ElementOf,
    SingleSubscript,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Triop {
    DoubleSubscript,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Finop {
    // Span,
    Plus, // normalize by associativity
    Times,
    And,
    Or,
    Forall,
    Exists,
    Max,
    Min,
    SeqLiteral,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum SeqOp {
    Sum,
    Prod,
    Map,
}
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
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

    pub fn with_default_metadata<NewMetadata: Default>(&self) -> Expr<NewMetadata> {
        let raw = match &self.raw {
            RawExpr::Hole => RawExpr::Hole,
            RawExpr::ImplicitDimension(dimension) => RawExpr::ImplicitDimension(*dimension),
            RawExpr::BoundNatural(index) => RawExpr::BoundNatural(*index),
            RawExpr::IdentityMatrix { dimension } => RawExpr::IdentityMatrix {
                dimension: *dimension,
            },
            RawExpr::StandardBasis { index, dimension } => RawExpr::StandardBasis {
                index: index.with_default_metadata(),
                dimension: *dimension,
            },
            RawExpr::ZeroMatrix { rows, cols } => RawExpr::ZeroMatrix {
                rows: *rows,
                cols: *cols,
            },
            RawExpr::Type(ty) => RawExpr::Type(ty.with_default_metadata()),
            RawExpr::Variable(variable) => RawExpr::Variable(variable.clone()),
            RawExpr::NatLiteral(value) => RawExpr::NatLiteral(*value),
            RawExpr::Matrix(matrix) => RawExpr::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .iter()
                    .map(Expr::with_default_metadata)
                    .collect(),
            }),
            RawExpr::Monop(op, expression) => {
                RawExpr::Monop(*op, expression.with_default_metadata())
            }
            RawExpr::Binop(op, left, right) => RawExpr::Binop(
                *op,
                left.with_default_metadata(),
                right.with_default_metadata(),
            ),
            RawExpr::Triop(op, first, second, third) => RawExpr::Triop(
                *op,
                first.with_default_metadata(),
                second.with_default_metadata(),
                third.with_default_metadata(),
            ),
            RawExpr::Finop(op, expressions) => RawExpr::Finop(
                *op,
                expressions
                    .iter()
                    .map(Expr::with_default_metadata)
                    .collect(),
            ),
            RawExpr::CmpChain(chain) => RawExpr::CmpChain(CmpChain {
                start: chain.start.with_default_metadata(),
                assertions: chain
                    .assertions
                    .iter()
                    .map(|(op, expression)| (*op, expression.with_default_metadata()))
                    .collect(),
            }),
            RawExpr::LogicChain(chain) => RawExpr::LogicChain(LogicChain {
                start: chain.start.with_default_metadata(),
                assertions: chain
                    .assertions
                    .iter()
                    .map(|(op, expression)| (*op, expression.with_default_metadata()))
                    .collect(),
            }),
            RawExpr::Seqop(op, range, body) => RawExpr::Seqop(
                *op,
                Range {
                    index_variable: range.index_variable.clone(),
                    from: range.from.with_default_metadata(),
                    to: range.to.with_default_metadata(),
                },
                body.with_default_metadata(),
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct MetaExpr<Metadata> {
    pub meta: Metadata,
    pub raw: RawExpr<Metadata>,
}
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Range<Metadata> {
    pub index_variable: Variable,
    pub from: Expr<Metadata>,
    pub to: Expr<Metadata>,
}
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CmpChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Cmp, Expr<Metadata>)>,
}
/// A sequence of adjacent logical relationships.
///
/// The chain `P implies Q implies R` means `(P implies Q) and
/// (Q implies R)`. It is neither associative implication nor an assertion
/// that `P` is true.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct LogicChain<Metadata> {
    pub start: Expr<Metadata>,
    pub assertions: Vec<(Logic, Expr<Metadata>)>,
}
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
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
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum RawExpr<Metadata> {
    Hole,
    /// An internal natural-valued leaf used to preserve a context-dependent
    /// matrix constant's dimension through symbolic typing.
    ImplicitDimension(ImplicitDimension),
    /// An internal de Bruijn reference to a one-based sequence position.
    BoundNatural(DeBruijnIndex),
    IdentityMatrix {
        dimension: ImplicitDimension,
    },
    StandardBasis {
        index: Expr<Metadata>,
        dimension: ImplicitDimension,
    },
    ZeroMatrix {
        rows: ImplicitDimension,
        cols: ImplicitDimension,
    },
    Type(TypeExpr<Metadata>),
    Variable(Variable),
    NatLiteral(u64),
    Matrix(Matrix<Expr<Metadata>>),
    Monop(Monop, Expr<Metadata>),
    Binop(Binop, Expr<Metadata>, Expr<Metadata>),
    Triop(Triop, Expr<Metadata>, Expr<Metadata>, Expr<Metadata>),
    Finop(Finop, Vec<Expr<Metadata>>),
    CmpChain(CmpChain<Metadata>),
    LogicChain(LogicChain<Metadata>),
    Seqop(SeqOp, Range<Metadata>, Expr<Metadata>),
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{
        Environment, Expr, Finop, ImplicitDimension, NaturalEvaluationError, NaturalParameter,
        RawExpr, TypeExpr, Variable,
    };

    struct MetadataWithoutClone;

    #[test]
    fn cloning_expr_does_not_require_cloneable_metadata() {
        let expression = Expr::with_metadata(MetadataWithoutClone, RawExpr::NatLiteral(1));
        let _clone = expression.clone();
    }

    #[test]
    fn default_metadata_preserves_holes() {
        let expression: Expr<()> = Expr::with_metadata(1, RawExpr::Hole).with_default_metadata();
        assert!(matches!(expression.raw, RawExpr::Hole));
    }

    #[test]
    fn natural_parameters_keep_variables_and_nonces_distinct() {
        let dimension = ImplicitDimension::fresh();
        assert_ne!(
            NaturalParameter::Variable(Variable::new(dimension.z3_name())),
            NaturalParameter::ImplicitDimension(dimension)
        );
    }

    #[test]
    fn evaluates_natural_expressions_used_by_symbolic_types() {
        let n = Variable::new("n");
        let dimension = ImplicitDimension::fresh();
        let environment = Environment {
            natural_assignment: HashMap::from([
                (NaturalParameter::Variable(n.clone()), 2),
                (NaturalParameter::ImplicitDimension(dimension), 1),
            ]),
        };
        let rows: Expr<()> = Expr::new(RawExpr::ImplicitDimension(dimension));
        let cols: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::Variable(n)),
                Expr::new(RawExpr::NatLiteral(1)),
            ],
        ));
        assert_eq!(environment.evaluate_natural(&cols), Ok(3));
        assert_eq!(environment.evaluate_natural(&rows), Ok(1));
    }

    #[test]
    fn natural_evaluation_reports_missing_assignments_and_overflow() {
        let missing: Expr<()> = Expr::new(RawExpr::Variable(Variable::new("n")));
        assert!(matches!(
            Environment::default().evaluate_natural(&missing),
            Err(NaturalEvaluationError::MissingAssignment(_))
        ));
        let overflow: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Times,
            vec![
                Expr::new(RawExpr::NatLiteral(u64::MAX)),
                Expr::new(RawExpr::NatLiteral(2)),
            ],
        ));
        assert_eq!(
            Environment::default().evaluate_natural(&overflow),
            Err(NaturalEvaluationError::Overflow)
        );
    }

    #[test]
    fn default_metadata_recursively_replaces_metadata() {
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

        let left: Expr<()> = expression(1).with_default_metadata();
        let right: Expr<()> = expression(2).with_default_metadata();
        assert_eq!(left, right);
    }

    #[test]
    fn default_metadata_replaces_symbolic_type_dimension_metadata() {
        let expression = Expr::with_metadata(
            1,
            RawExpr::Type(TypeExpr::Matrix(
                Expr::with_metadata(2, RawExpr::Variable(Variable::new("n"))),
                Expr::with_metadata(
                    3,
                    RawExpr::Finop(
                        Finop::Plus,
                        vec![
                            Expr::with_metadata(4, RawExpr::Variable(Variable::new("d"))),
                            Expr::with_metadata(5, RawExpr::Variable(Variable::new("p"))),
                        ],
                    ),
                ),
            )),
        );
        let erased: Expr<()> = expression.with_default_metadata();
        assert!(matches!(erased.raw, RawExpr::Type(TypeExpr::Matrix(_, _))));
    }

    #[test]
    fn default_metadata_replaces_sequence_element_and_size_metadata() {
        fn sequence(metadata: u8) -> Expr<u8> {
            Expr::with_metadata(
                metadata,
                RawExpr::Type(TypeExpr::Seq(
                    Expr::with_metadata(
                        metadata + 1,
                        RawExpr::Type(TypeExpr::Matrix(
                            Expr::with_metadata(
                                metadata + 2,
                                RawExpr::Variable(Variable::new("d")),
                            ),
                            Expr::with_metadata(metadata + 3, RawExpr::NatLiteral(1)),
                        )),
                    ),
                    Expr::with_metadata(metadata + 4, RawExpr::Variable(Variable::new("n"))),
                )),
            )
        }

        assert_eq!(
            sequence(1).with_default_metadata::<()>(),
            sequence(10).with_default_metadata::<()>()
        );
    }

    #[test]
    fn default_metadata_preserves_implicit_dimension_identity() {
        let dimension = ImplicitDimension::fresh();
        let expression = Expr::with_metadata(
            1,
            RawExpr::StandardBasis {
                index: Expr::with_metadata(2, RawExpr::Variable(Variable::new("i"))),
                dimension,
            },
        );
        assert!(matches!(
            expression.with_default_metadata::<()>().raw,
            RawExpr::StandardBasis {
                dimension: found,
                ..
            } if found == dimension
        ));
    }
}
