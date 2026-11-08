//! Structural expression encoding for QF_DT queries.
//!
//! Arithmetic and quantifiers are syntax, not SMT operations. Callers supply
//! already lowered core expressions; this module performs no typing or rewriting.
//! Finite operations retain their argument lists, including empty and singleton
//! lists, without assigning them mathematical validity. Comparison chains become
//! conjunctions of adjacent comparisons. Quantifier premises and nested sequences
//! also retain their list structure.
//!
//! Variables and implicit dimensions use codec-local IDs. Decode evaluated model
//! values with the same codec. Independent codecs in one Z3 context must use
//! distinct namespaces; one codec can be reused with multiple solvers.
//!
//! ```
//! use linalg_sandbox::{Expr, RawExpr, smt_dt::ExprDatatype};
//! use z3::{Solver, SatResult};
//! let mut codec = ExprDatatype::new("example");
//! let solver = Solver::new_for_logic("QF_DT").unwrap();
//! let term = codec.constant("term");
//! let expression = Expr::<()>::new(RawExpr::NatLiteral(3));
//! codec.assert_equal(&solver, &term, &expression).unwrap();
//! assert_eq!(solver.check(), SatResult::Sat);
//! let value = solver.get_model().unwrap().eval(&term, true).unwrap();
//! assert_eq!(codec.decode(&value).unwrap(), expression);
//! // solver.to_smt2() includes the referenced datatype declarations.
//! ```

mod proof;
mod schema;
pub use proof::{ProofDatatype, ProofNode, ProofRule, selector_child};
#[cfg(test)]
mod proof_tests;
#[cfg(test)]
mod tests;

use crate::{
    CmpChain, DeBruijnIndex, Expr, Finop, ImplicitDimension, Logic, LogicChain, Matrix, Range,
    RawExpr, TypeExpr, Variable,
};
use schema::{Schema, app, field, tag};
use std::{collections::HashMap, fmt, hash::Hash};
use z3::{
    DatatypeSort, Solver, Symbol,
    ast::{Ast, Datatype},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Unsupported(&'static str),
    Malformed(&'static str),
    WrongSort,
    UnregisteredDatatype,
    UnevaluatedTerm,
    UnknownAtom { kind: &'static str, id: u64 },
    NumericOverflow,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(kind) => write!(f, "unsupported core expression: {kind}"),
            Self::Malformed(reason) => write!(f, "malformed datatype expression: {reason}"),
            Self::UnregisteredDatatype => f.write_str("parent datatype is not registered"),
            Self::WrongSort => f.write_str("term has a different datatype sort"),
            Self::UnevaluatedTerm => f.write_str("expected an evaluated constructor term"),
            Self::UnknownAtom { kind, id } => write!(f, "unknown {kind} ID {id} in this codec"),
            Self::NumericOverflow => {
                f.write_str("datatype numeral does not fit the expression's numeric range")
            }
        }
    }
}
impl std::error::Error for Error {}

struct Atoms<T> {
    ids: HashMap<T, u64>,
    values: Vec<T>,
}
impl<T> Default for Atoms<T> {
    fn default() -> Self {
        Self {
            ids: HashMap::new(),
            values: Vec::new(),
        }
    }
}
impl<T: Eq + Hash + Clone> Atoms<T> {
    fn intern(&mut self, value: &T) -> Result<u64, Error> {
        if let Some(id) = self.ids.get(value) {
            return Ok(*id);
        }
        let id = u64::try_from(self.values.len()).map_err(|_| Error::NumericOverflow)?;
        self.values.push(value.clone());
        self.ids.insert(value.clone(), id);
        Ok(id)
    }
    fn get(&self, id: u64, kind: &'static str) -> Result<T, Error> {
        usize::try_from(id)
            .ok()
            .and_then(|i| self.values.get(i))
            .cloned()
            .ok_or(Error::UnknownAtom { kind, id })
    }
}

/// Datatype definitions and the vocabulary needed to decode their model values.
///
/// `namespace` prefixes every datatype, constructor, and selector. Z3 creates
/// sorts in its thread-local context, not in a particular solver. A solver's
/// `to_smt2()` prints the definitions once an assertion references these sorts.
pub struct ExprDatatype {
    schema: Schema,
    variables: Atoms<Variable>,
    dimensions: Atoms<ImplicitDimension>,
}
impl ExprDatatype {
    pub fn new(namespace: &str) -> Self {
        Self {
            schema: Schema::new(namespace),
            variables: Atoms::default(),
            dimensions: Atoms::default(),
        }
    }
    pub fn sort(&self) -> &DatatypeSort {
        &self.schema.expr
    }
    /// All datatype definitions belonging to this codec, for selector inspection.
    pub fn datatypes(&self) -> [&DatatypeSort; 11] {
        let s = &self.schema;
        [
            &s.natural,
            &s.positive,
            &s.monop.sort,
            &s.binop.sort,
            &s.finop.sort,
            &s.quantifier.sort,
            &s.comparison.sort,
            &s.seqop.sort,
            &s.expr,
            &s.ty,
            &s.list,
        ]
    }
    /// Construct an operator application containing symbolic expression terms.
    pub fn finite(&self, op: Finop, arguments: &[Datatype]) -> Result<Datatype, Error> {
        if arguments
            .iter()
            .any(|a| a.get_sort() != self.schema.expr.sort)
        {
            return Err(Error::WrongSort);
        }
        Ok(self.node(
            "Finite",
            &[self.schema.finop.encode(op)?, self.list(arguments.to_vec())],
        ))
    }
    pub fn constant(&self, name: impl Into<Symbol>) -> Datatype {
        Datatype::new_const(name, &self.schema.expr.sort)
    }

    /// Assert structural equality, committing no solver assertion on failure.
    pub fn assert_equal<M>(
        &mut self,
        solver: &Solver,
        term: &Datatype,
        expression: &Expr<M>,
    ) -> Result<(), Error> {
        if term.get_sort() != self.schema.expr.sort {
            return Err(Error::WrongSort);
        }
        let encoded = self.encode(expression)?;
        solver.assert(term.eq(&encoded));
        Ok(())
    }
    fn variable(&mut self, v: &Variable) -> Result<Datatype, Error> {
        let id = self.variables.intern(v)?;
        Ok(self.schema.natural(id))
    }
    fn dimension(&mut self, d: &ImplicitDimension) -> Result<Datatype, Error> {
        let id = self.dimensions.intern(d)?;
        Ok(self.schema.natural(id))
    }
    fn node(&self, name: &str, fields: &[Datatype]) -> Datatype {
        app(&self.schema.expr, name, fields)
    }

    /// Encode syntax, ignoring metadata. Unsupported surface forms must first
    /// pass through the existing rewrite pipeline. Atom IDs follow source order.
    pub fn encode<M>(&mut self, expression: &Expr<M>) -> Result<Datatype, Error> {
        let (name, fields) = match &expression.raw {
            RawExpr::Variable(v) => ("Var", vec![self.variable(v)?]),
            RawExpr::NatLiteral(n) => ("NatLiteral", vec![self.schema.natural(*n)]),
            RawExpr::BoolLiteral(value) => {
                return Ok(self
                    .schema
                    .expr
                    .variants
                    .iter()
                    .find(|v| v.constructor.name().ends_with(".BoolLiteral"))
                    .unwrap()
                    .constructor
                    .apply(&[&z3::ast::Bool::from_bool(*value)])
                    .as_datatype()
                    .unwrap());
            }
            RawExpr::Type(ty) => ("TypeValue", vec![self.encode_type(ty)?]),
            RawExpr::ImplicitDimension(d) => ("Implicit", vec![self.dimension(d)?]),
            RawExpr::BoundNatural(i) => (
                "Bound",
                vec![
                    self.schema
                        .natural(u64::try_from(i.get()).map_err(|_| Error::NumericOverflow)?),
                ],
            ),
            RawExpr::IdentityMatrix { dimension } => ("Identity", vec![self.dimension(dimension)?]),
            RawExpr::ZeroMatrix { rows, cols } => {
                ("Zero", vec![self.dimension(rows)?, self.dimension(cols)?])
            }
            RawExpr::StandardBasis { index, dimension } => (
                "Basis",
                vec![self.encode(index)?, self.dimension(dimension)?],
            ),
            RawExpr::EmptySet => ("EmptySet", vec![]),
            RawExpr::Matrix(matrix) => {
                check_matrix(matrix.rows, matrix.cols, matrix.elements.len())?;
                let rows = self
                    .schema
                    .natural(u64::try_from(matrix.rows).map_err(|_| Error::NumericOverflow)?);
                let cols = self
                    .schema
                    .natural(u64::try_from(matrix.cols).map_err(|_| Error::NumericOverflow)?);
                (
                    "MatrixLiteral",
                    vec![rows, cols, self.encode_list(&matrix.elements)?],
                )
            }
            RawExpr::Monop(op, value) => (
                "Unary",
                vec![self.schema.monop.encode(*op)?, self.encode(value)?],
            ),
            RawExpr::Binop(op, left, right) => (
                "Binary",
                vec![
                    self.schema.binop.encode(*op)?,
                    self.encode(left)?,
                    self.encode(right)?,
                ],
            ),
            RawExpr::Finop(op @ (Finop::Forall | Finop::Exists), values) => {
                if values.len() < 2 {
                    return Err(Error::Malformed("quantifier requires premises and a body"));
                }
                (
                    "Quantified",
                    vec![
                        self.schema.quantifier.encode(*op)?,
                        self.encode_list(&values[..values.len() - 1])?,
                        self.encode(values.last().unwrap())?,
                    ],
                )
            }
            RawExpr::Finop(Finop::SeqLiteral, values) => {
                if values.len() < 2 {
                    return Err(Error::Malformed(
                        "sequence literal requires at least two elements",
                    ));
                }
                ("SequenceLiteral", vec![self.encode_list(values)?])
            }
            RawExpr::Finop(op, values) => {
                let op = self.schema.finop.encode(*op)?;
                ("Finite", vec![op, self.encode_list(values)?])
            }
            RawExpr::CmpChain(chain) => {
                if chain.assertions.is_empty() {
                    return Err(Error::Malformed("comparison requires a relation"));
                }
                let mut left = self.encode(&chain.start)?;
                let mut clauses = Vec::new();
                for (op, right) in &chain.assertions {
                    let right = self.encode(right)?;
                    clauses.push(self.node(
                        "Compare",
                        &[self.schema.comparison.encode(*op)?, left, right.clone()],
                    ));
                    left = right;
                }
                if clauses.len() == 1 {
                    return Ok(clauses.pop().unwrap());
                }
                return Ok(self.node(
                    "Finite",
                    &[self.schema.finop.encode(Finop::And)?, self.list(clauses)],
                ));
            }
            RawExpr::LogicChain(chain) => {
                let [(Logic::Imp, right)] = chain.assertions.as_slice() else {
                    return Err(Error::Unsupported("logic chain requires logic lowering"));
                };
                (
                    "Implies",
                    vec![self.encode(&chain.start)?, self.encode(right)?],
                )
            }
            RawExpr::Seqop(op, range, body) => (
                "SequenceOp",
                vec![
                    self.schema.seqop.encode(*op)?,
                    self.variable(&range.index_variable)?,
                    self.encode(&range.from)?,
                    self.encode(&range.to)?,
                    self.encode(body)?,
                ],
            ),
            RawExpr::SetComprehension {
                variable,
                domain,
                predicate,
            } => (
                "Comprehension",
                vec![
                    self.variable(variable)?,
                    self.encode_type(domain)?,
                    self.encode(predicate)?,
                ],
            ),
            RawExpr::Hole => return Err(Error::Unsupported("hole")),
            RawExpr::Ellipsis => return Err(Error::Unsupported("ellipsis")),
            RawExpr::Triop(..) => return Err(Error::Unsupported("ternary operator")),
        };
        Ok(self.node(name, &fields))
    }
    fn encode_list<M>(&mut self, values: &[Expr<M>]) -> Result<Datatype, Error> {
        let values = values
            .iter()
            .map(|e| self.encode(e))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(self.list(values))
    }
    fn list(&self, values: Vec<Datatype>) -> Datatype {
        let mut result = app(&self.schema.list, "ExprNil", &[]);
        for value in values.into_iter().rev() {
            result = app(&self.schema.list, "ExprCons", &[value, result]);
        }
        result
    }
    fn encode_type<M>(&mut self, ty: &TypeExpr<M>) -> Result<Datatype, Error> {
        let (name, fields) = match ty {
            TypeExpr::Bool => ("BoolType", vec![]),
            TypeExpr::Nat => ("NatType", vec![]),
            TypeExpr::Int => ("IntType", vec![]),
            TypeExpr::Real => ("RealType", vec![]),
            TypeExpr::Set(element) => ("SetType", vec![self.encode_type(element)?]),
            TypeExpr::Matrix(rows, cols) => {
                ("MatrixType", vec![self.encode(rows)?, self.encode(cols)?])
            }
            TypeExpr::Seq(element, length) => (
                "SequenceType",
                vec![self.encode(element)?, self.encode(length)?],
            ),
        };
        Ok(app(&self.schema.ty, name, &fields))
    }

    /// Decode an evaluated model term using this codec's registered atom IDs.
    /// No new variables or implicit dimensions are invented for unknown IDs.
    pub fn decode(&self, value: &Datatype) -> Result<Expr<()>, Error> {
        let raw = match tag(value, &self.schema.expr)?.as_str() {
            "Var" => RawExpr::Variable(self.read_variable(&field(value, 0)?)?),
            "NatLiteral" => RawExpr::NatLiteral(self.schema.read_natural(&field(value, 0)?)?),
            "BoolLiteral" => RawExpr::BoolLiteral(
                value
                    .nth_child(0)
                    .and_then(|e| e.as_bool())
                    .and_then(|e| e.as_bool())
                    .ok_or(Error::UnevaluatedTerm)?,
            ),
            "TypeValue" => RawExpr::Type(self.decode_type(&field(value, 0)?)?),
            "Implicit" => RawExpr::ImplicitDimension(self.read_dimension(&field(value, 0)?)?),
            "Bound" => {
                RawExpr::BoundNatural(DeBruijnIndex::new(self.read_size(&field(value, 0)?)?))
            }
            "Identity" => RawExpr::IdentityMatrix {
                dimension: self.read_dimension(&field(value, 0)?)?,
            },
            "Zero" => RawExpr::ZeroMatrix {
                rows: self.read_dimension(&field(value, 0)?)?,
                cols: self.read_dimension(&field(value, 1)?)?,
            },
            "Basis" => RawExpr::StandardBasis {
                index: self.decode(&field(value, 0)?)?,
                dimension: self.read_dimension(&field(value, 1)?)?,
            },
            "EmptySet" => RawExpr::EmptySet,
            "MatrixLiteral" => {
                let rows = self.read_size(&field(value, 0)?)?;
                let cols = self.read_size(&field(value, 1)?)?;
                let elements = self.decode_list(&field(value, 2)?)?;
                check_matrix(rows, cols, elements.len())?;
                RawExpr::Matrix(Matrix {
                    rows,
                    cols,
                    elements,
                })
            }
            "Unary" => RawExpr::Monop(
                self.schema.monop.decode(&field(value, 0)?)?,
                self.decode(&field(value, 1)?)?,
            ),
            "Binary" => RawExpr::Binop(
                self.schema.binop.decode(&field(value, 0)?)?,
                self.decode(&field(value, 1)?)?,
                self.decode(&field(value, 2)?)?,
            ),
            "Finite" => RawExpr::Finop(
                self.schema.finop.decode(&field(value, 0)?)?,
                self.decode_list(&field(value, 1)?)?,
            ),
            "Compare" => RawExpr::CmpChain(CmpChain {
                start: self.decode(&field(value, 1)?)?,
                assertions: vec![(
                    self.schema.comparison.decode(&field(value, 0)?)?,
                    self.decode(&field(value, 2)?)?,
                )],
            }),
            "Implies" => RawExpr::LogicChain(LogicChain {
                start: self.decode(&field(value, 0)?)?,
                assertions: vec![(Logic::Imp, self.decode(&field(value, 1)?)?)],
            }),
            "Quantified" => {
                let op = self.schema.quantifier.decode(&field(value, 0)?)?;
                let mut values = self.decode_list(&field(value, 1)?)?;
                if values.is_empty() {
                    return Err(Error::Malformed("quantifier requires a premise"));
                }
                values.push(self.decode(&field(value, 2)?)?);
                RawExpr::Finop(op, values)
            }
            "SequenceLiteral" => {
                let values = self.decode_list(&field(value, 0)?)?;
                if values.len() < 2 {
                    return Err(Error::Malformed(
                        "sequence literal requires at least two elements",
                    ));
                }
                RawExpr::Finop(Finop::SeqLiteral, values)
            }
            "SequenceOp" => RawExpr::Seqop(
                self.schema.seqop.decode(&field(value, 0)?)?,
                Range {
                    index_variable: self.read_variable(&field(value, 1)?)?,
                    from: self.decode(&field(value, 2)?)?,
                    to: self.decode(&field(value, 3)?)?,
                },
                self.decode(&field(value, 4)?)?,
            ),
            "Comprehension" => RawExpr::SetComprehension {
                variable: self.read_variable(&field(value, 0)?)?,
                domain: self.decode_type(&field(value, 1)?)?,
                predicate: self.decode(&field(value, 2)?)?,
            },
            _ => return Err(Error::Malformed("unexpected expression constructor")),
        };
        Ok(Expr::new(raw))
    }
    fn read_variable(&self, value: &Datatype) -> Result<Variable, Error> {
        self.variables
            .get(self.schema.read_natural(value)?, "variable")
    }
    fn read_dimension(&self, value: &Datatype) -> Result<ImplicitDimension, Error> {
        self.dimensions
            .get(self.schema.read_natural(value)?, "implicit dimension")
    }
    fn read_size(&self, value: &Datatype) -> Result<usize, Error> {
        usize::try_from(self.schema.read_natural(value)?).map_err(|_| Error::NumericOverflow)
    }
    fn decode_list(&self, value: &Datatype) -> Result<Vec<Expr<()>>, Error> {
        let mut tail = value.clone();
        let mut result = Vec::new();
        loop {
            match tag(&tail, &self.schema.list)?.as_str() {
                "ExprNil" => return Ok(result),
                "ExprCons" => {
                    result.push(self.decode(&field(&tail, 0)?)?);
                    tail = field(&tail, 1)?;
                }
                _ => return Err(Error::Malformed("unexpected list constructor")),
            }
        }
    }
    fn decode_type(&self, value: &Datatype) -> Result<TypeExpr<()>, Error> {
        Ok(match tag(value, &self.schema.ty)?.as_str() {
            "BoolType" => TypeExpr::Bool,
            "NatType" => TypeExpr::Nat,
            "IntType" => TypeExpr::Int,
            "RealType" => TypeExpr::Real,
            "SetType" => TypeExpr::Set(Box::new(self.decode_type(&field(value, 0)?)?)),
            "MatrixType" => TypeExpr::Matrix(
                self.decode(&field(value, 0)?)?,
                self.decode(&field(value, 1)?)?,
            ),
            "SequenceType" => TypeExpr::Seq(
                self.decode(&field(value, 0)?)?,
                self.decode(&field(value, 1)?)?,
            ),
            _ => return Err(Error::Malformed("unexpected type constructor")),
        })
    }
}
fn check_matrix(rows: usize, cols: usize, len: usize) -> Result<(), Error> {
    if rows.checked_mul(cols).ok_or(Error::NumericOverflow)? != len || (rows == 0) != (cols == 0) {
        Err(Error::Malformed("matrix dimensions do not match its cells"))
    } else {
        Ok(())
    }
}
