use std::{collections::HashMap, error::Error, fmt};

use crate::{
    Binop, Environment, Expr, Finop, LogicChain, Matrix, Monop, RawExpr, Type, TypeExpr, Variable,
    visit_mut::{VisitContext, VisitMut},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    MissingType(Variable),
    Invalid(&'static str),
    Unsupported(&'static str),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingType(variable) => write!(f, "missing type for {}", variable.z3_name()),
            Self::Invalid(message) | Self::Unsupported(message) => f.write_str(message),
        }
    }
}

impl Error for TypeError {}

pub trait MaybeTyped {
    fn get_type(&self) -> Result<TypeExpr<()>, TypeError>;
    fn put_type(&mut self, ty: TypeExpr<()>);
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypedMetadata(Option<TypeExpr<()>>);

impl MaybeTyped for TypedMetadata {
    fn get_type(&self) -> Result<TypeExpr<()>, TypeError> {
        self.0
            .clone()
            .ok_or(TypeError::Unsupported("expression has no value type"))
    }

    fn put_type(&mut self, ty: TypeExpr<()>) {
        self.0 = Some(ty);
    }
}

pub trait TypeLookup {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolicTypeEnvironment {
    pub types: HashMap<Variable, TypeExpr<()>>,
}

impl TypeLookup for SymbolicTypeEnvironment {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>> {
        self.types.get(variable).cloned()
    }
}

impl TypeLookup for Environment {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>> {
        self.types
            .get(variable)
            .cloned()
            .map(type_expr)
            .or_else(|| {
                self.equalities
                    .contains_key(&Expr::new(RawExpr::Variable(variable.clone())))
                    .then_some(TypeExpr::Nat)
            })
    }
}

pub struct TypeResolver<'a, Lookup> {
    types: &'a Lookup,
    lexical_types: HashMap<Variable, TypeExpr<()>>,
    error: Option<TypeError>,
}

impl<'a, Lookup: TypeLookup> TypeResolver<'a, Lookup> {
    pub fn new(types: &'a Lookup) -> Self {
        Self {
            types,
            lexical_types: HashMap::new(),
            error: None,
        }
    }

    pub fn resolve<Metadata: MaybeTyped>(
        mut self,
        expression: &mut Expr<Metadata>,
        context: VisitContext,
    ) -> Result<(), TypeError> {
        self.visit_expr_mut(context, expression);
        self.error.map_or(Ok(()), Err)
    }

    fn infer<Metadata: MaybeTyped>(
        &self,
        expression: &Expr<Metadata>,
    ) -> Result<Option<TypeExpr<()>>, TypeError> {
        let ty = match &expression.raw {
            RawExpr::Hole | RawExpr::Type(_) => return Ok(None),
            RawExpr::IdentityMatrix { dimension } => {
                let dimension = implicit_dimension(*dimension);
                TypeExpr::Matrix(dimension.clone(), dimension)
            }
            RawExpr::StandardBasis { dimension, .. } => {
                TypeExpr::Matrix(implicit_dimension(*dimension), natural(1))
            }
            RawExpr::ZeroMatrix { rows, cols } => {
                TypeExpr::Matrix(implicit_dimension(*rows), implicit_dimension(*cols))
            }
            RawExpr::Variable(variable) => self
                .lexical_types
                .get(variable)
                .cloned()
                .or_else(|| self.types.type_of(variable))
                .unwrap_or_else(|| {
                    panic!(
                        "variable {} has no symbolically inferred type",
                        variable.z3_name()
                    )
                }),
            RawExpr::NatLiteral(_) => TypeExpr::Nat,
            RawExpr::Matrix(Matrix { rows, cols, .. }) => {
                TypeExpr::Matrix(natural(*rows as u64), natural(*cols as u64))
            }
            RawExpr::Monop(op, inner) => infer_monop(*op, node_type(inner)?)?,
            RawExpr::Binop(Binop::ElementOf, _, _) => TypeExpr::Bool,
            RawExpr::Binop(Binop::Cast, target, _) => {
                let RawExpr::Type(target) = &target.raw else {
                    return Ok(None);
                };
                erase_type_metadata(target)
            }
            RawExpr::Binop(Binop::SingleSubscript, sequence, _) => {
                let TypeExpr::Seq(element, _) = node_type(sequence)? else {
                    return Err(TypeError::Invalid(
                        "subscripted expression is not a sequence",
                    ));
                };
                let RawExpr::Type(element) = &element.raw else {
                    return Err(TypeError::Invalid(
                        "sequence element must be a type expression",
                    ));
                };
                element.clone()
            }
            RawExpr::Binop(Binop::Power, base, _) => node_type(base)?,
            RawExpr::Binop(Binop::Div, left, right) => {
                division_type(node_type(left)?, node_type(right)?)?
            }
            RawExpr::Binop(Binop::InnerProd, _, _) => TypeExpr::Real,
            RawExpr::Triop(_, _, _, _) => TypeExpr::Real,
            RawExpr::Finop(Finop::And | Finop::Or, _) => TypeExpr::Bool,
            RawExpr::Finop(Finop::Plus | Finop::Times, expressions) if expressions.is_empty() => {
                return Ok(None);
            }
            RawExpr::Finop(Finop::Plus, expressions) => fold_types(expressions, add_type)?,
            RawExpr::Finop(Finop::Times, expressions) => fold_types(expressions, multiply_type)?,
            RawExpr::Finop(Finop::Max | Finop::Min, expressions) => {
                fold_types(expressions, scalar_lub)?
            }
            RawExpr::CmpChain(_) | RawExpr::LogicChain(_) => TypeExpr::Bool,
            RawExpr::Seqop(_, _, body) => node_type(body)?,
        };
        Ok(Some(ty))
    }
}

impl<Metadata: MaybeTyped, Lookup: TypeLookup> VisitMut<Metadata> for TypeResolver<'_, Lookup> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        let _logical_polarity = context.logical_polarity;
        if self.error.is_some() {
            return;
        }
        {
            let raw = &mut node
                .get_mut()
                .expect("type resolution requires unique expressions")
                .raw;
            match raw {
                RawExpr::Hole
                | RawExpr::IdentityMatrix { .. }
                | RawExpr::ZeroMatrix { .. }
                | RawExpr::Variable(_)
                | RawExpr::NatLiteral(_) => {}
                RawExpr::StandardBasis { index, .. } => self.visit_expr_mut(context, index),
                RawExpr::Type(_) => {}
                RawExpr::Matrix(matrix) => {
                    for element in &mut matrix.elements {
                        self.visit_expr_mut(context, element);
                    }
                }
                RawExpr::Monop(_, inner) => self.visit_expr_mut(context, inner),
                RawExpr::Binop(Binop::ElementOf, left, right) => {
                    if !matches!(left.raw, RawExpr::Variable(_)) {
                        self.visit_expr_mut(context, left);
                    }
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Binop(Binop::Cast, _, value) => self.visit_expr_mut(context, value),
                RawExpr::Binop(_, left, right) => {
                    self.visit_expr_mut(context, left);
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Triop(_, a, b, c) => {
                    self.visit_expr_mut(context, a);
                    self.visit_expr_mut(context, b);
                    self.visit_expr_mut(context, c);
                }
                RawExpr::Finop(_, expressions) => {
                    for expression in expressions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::CmpChain(chain) => {
                    self.visit_expr_mut(context, &mut chain.start);
                    for (_, expression) in &mut chain.assertions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::LogicChain(LogicChain { start, assertions }) => {
                    self.visit_expr_mut(context, start);
                    for (_, expression) in assertions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::Seqop(_, range, body) => {
                    self.visit_expr_mut(context, &mut range.from);
                    self.visit_expr_mut(context, &mut range.to);
                    let previous = self
                        .lexical_types
                        .insert(range.index_variable.clone(), TypeExpr::Nat);
                    self.visit_expr_mut(context, body);
                    if let Some(previous) = previous {
                        self.lexical_types
                            .insert(range.index_variable.clone(), previous);
                    } else {
                        self.lexical_types.remove(&range.index_variable);
                    }
                }
            }
        }
        match self.infer(node) {
            Ok(Some(ty)) => node.get_mut().unwrap().meta.put_type(ty),
            Ok(None) => {}
            Err(error) => self.error = Some(error),
        }
    }
}

fn node_type<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> Result<TypeExpr<()>, TypeError> {
    expression.meta.get_type()
}

fn erase_type_metadata<Metadata>(ty: &TypeExpr<Metadata>) -> TypeExpr<()> {
    match ty {
        TypeExpr::Bool => TypeExpr::Bool,
        TypeExpr::Nat => TypeExpr::Nat,
        TypeExpr::Int => TypeExpr::Int,
        TypeExpr::Real => TypeExpr::Real,
        TypeExpr::Matrix(rows, cols) => {
            TypeExpr::Matrix(rows.with_default_metadata(), cols.with_default_metadata())
        }
        TypeExpr::Seq(element, size) => TypeExpr::Seq(
            element.with_default_metadata(),
            size.with_default_metadata(),
        ),
    }
}

pub(crate) fn type_expr(ty: Type) -> TypeExpr<()> {
    match ty {
        Type::Bool => TypeExpr::Bool,
        Type::Nat => TypeExpr::Nat,
        Type::Int => TypeExpr::Int,
        Type::Real => TypeExpr::Real,
        Type::Matrix(rows, cols) => TypeExpr::Matrix(natural(rows), natural(cols)),
        Type::Seq(sequence) => TypeExpr::Seq(
            Expr::new(RawExpr::Type(type_expr(sequence.t))),
            natural(sequence.n),
        ),
    }
}

fn natural(value: u64) -> Expr<()> {
    Expr::new(RawExpr::NatLiteral(value))
}
fn implicit_dimension(value: crate::ImplicitDimension) -> Expr<()> {
    Expr::new(RawExpr::Variable(Variable::new(value.z3_name())))
}

fn infer_monop(op: Monop, inner: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match op {
        Monop::Neg => require_numeric(inner),
        Monop::Transpose => match inner {
            TypeExpr::Matrix(r, c) => Ok(TypeExpr::Matrix(c, r)),
            _ => Err(TypeError::Invalid("transpose requires a matrix")),
        },
        Monop::Trace
        | Monop::Det
        | Monop::Norm1
        | Monop::Norm2
        | Monop::NormInfty
        | Monop::NormFrob => Ok(TypeExpr::Real),
        Monop::Inverse => match inner {
            matrix @ TypeExpr::Matrix(_, _) => Ok(matrix),
            _ => Err(TypeError::Invalid("inverse requires a matrix")),
        },
    }
}

type BinaryTypeOperation = fn(TypeExpr<()>, TypeExpr<()>) -> Result<TypeExpr<()>, TypeError>;

fn fold_types<Metadata: MaybeTyped>(
    expressions: &[Expr<Metadata>],
    op: BinaryTypeOperation,
) -> Result<TypeExpr<()>, TypeError> {
    let mut expressions = expressions.iter();
    let first = expressions
        .next()
        .ok_or(TypeError::Invalid("finite operation is empty"))?;
    expressions.try_fold(node_type(first)?, |left, right| op(left, node_type(right)?))
}

fn require_numeric(ty: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match ty {
        TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real | TypeExpr::Matrix(_, _) => Ok(ty),
        _ => Err(TypeError::Invalid("operation requires numeric operands")),
    }
}

fn scalar_lub(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (TypeExpr::Nat, TypeExpr::Nat) => Ok(TypeExpr::Nat),
        (TypeExpr::Nat | TypeExpr::Int, TypeExpr::Nat | TypeExpr::Int) => Ok(TypeExpr::Int),
        (
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
        ) => Ok(TypeExpr::Real),
        _ => Err(TypeError::Invalid(
            "operation requires numeric scalar operands",
        )),
    }
}

fn add_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (matrix @ TypeExpr::Matrix(_, _), TypeExpr::Matrix(_, _)) => Ok(matrix),
        (TypeExpr::Matrix(_, _), _) | (_, TypeExpr::Matrix(_, _)) => Err(TypeError::Invalid(
            "matrix and scalar addition is unsupported",
        )),
        (left, right) => scalar_lub(left, right),
    }
}

fn multiply_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (TypeExpr::Matrix(rows, _), TypeExpr::Matrix(_, cols)) => Ok(TypeExpr::Matrix(rows, cols)),
        (matrix @ TypeExpr::Matrix(_, _), scalar) | (scalar, matrix @ TypeExpr::Matrix(_, _)) => {
            require_numeric(scalar)?;
            Ok(matrix)
        }
        (left, right) => scalar_lub(left, right),
    }
}

fn division_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    let scalar = |ty| match ty {
        TypeExpr::Matrix(_, _) => Ok(TypeExpr::Real),
        other => Ok(other),
    };
    scalar_lub(scalar(left)?, scalar(right)?)
}

#[cfg(test)]
mod tests {
    use super::{MaybeTyped, SymbolicTypeEnvironment, TypeResolver, TypedMetadata};
    use crate::{Expr, RawExpr, TypeExpr, Variable, from_tex, visit_mut::VisitContext};
    use ratex_parser::parse;
    use std::collections::HashMap;

    #[test]
    fn resolves_symbolic_matrix_dimensions_without_concretizing_them() {
        let n = Expr::new(RawExpr::Variable(Variable::new("n")));
        let p = Expr::new(RawExpr::Variable(Variable::new("p")));
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([
                (Variable::new("A"), TypeExpr::Matrix(n.clone(), p.clone())),
                (Variable::new("B"), TypeExpr::Matrix(p, n.clone())),
            ]),
        };
        let parsed: Expr<()> = from_tex::expr(&parse("A B").unwrap()).unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        TypeResolver::new(&types)
            .resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true,
                },
            )
            .unwrap();
        assert_eq!(
            expression.meta.get_type().unwrap(),
            TypeExpr::Matrix(n.clone(), n)
        );
    }
}
