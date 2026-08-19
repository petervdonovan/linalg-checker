use std::{collections::HashMap, error::Error, fmt};

use crate::{
    Binop, Environment, Expr, Finop, LogicChain, Matrix, Monop, RawExpr, SeqType, Type,
    TypeExpr, Variable,
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

pub struct TypeResolver<'a> {
    environment: &'a Environment,
    lexical_types: HashMap<Variable, Type>,
}

impl<'a> TypeResolver<'a> {
    pub fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            lexical_types: HashMap::new(),
        }
    }

    pub fn resolve<Metadata: MaybeTyped>(
        mut self,
        expression: &mut Expr<Metadata>,
        context: VisitContext,
    ) -> Result<(), TypeError> {
        self.visit_expr_mut(context, expression);
        Ok(())
    }

    fn record<T>(&mut self, result: Result<T, TypeError>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(error) => {
                let _ = error;
                None
            }
        }
    }

    fn infer<Metadata: MaybeTyped>(
        &self,
        expression: &Expr<Metadata>,
    ) -> Result<Option<Type>, TypeError> {
        let ty = match &expression.raw {
            RawExpr::Hole | RawExpr::Type(_) => return Ok(None),
            RawExpr::IdentityMatrix { dimension } => {
                let n = self.implicit_dimension(*dimension)?;
                Type::Matrix(n, n)
            }
            RawExpr::StandardBasis { dimension, .. } => {
                Type::Matrix(self.implicit_dimension(*dimension)?, 1)
            }
            RawExpr::ZeroMatrix { rows, cols } => Type::Matrix(
                self.implicit_dimension(*rows)?,
                self.implicit_dimension(*cols)?,
            ),
            RawExpr::Variable(variable) => self
                .lexical_types
                .get(variable)
                .or_else(|| self.environment.types.get(variable))
                .cloned()
                .or_else(|| {
                    let key = Expr::new(RawExpr::Variable(variable.clone()));
                    self.environment.equalities.contains_key(&key).then_some(Type::Nat)
                })
                .ok_or_else(|| TypeError::MissingType(variable.clone()))?,
            RawExpr::NatLiteral(_) => Type::Nat,
            RawExpr::Matrix(Matrix { rows, cols, .. }) => {
                Type::Matrix(*rows as u64, *cols as u64)
            }
            RawExpr::Monop(op, inner) => self.infer_monop(*op, node_type(inner)?)?,
            RawExpr::Binop(Binop::ElementOf, _, _) => Type::Bool,
            RawExpr::Binop(Binop::Cast, target, value) => {
                let RawExpr::Type(target) = &target.raw else {
                    return Err(TypeError::Invalid("cast target must be a type expression"));
                };
                let source = node_type(value)?;
                let target = self.concrete_type_expr(target)?;
                match (&source, &target) {
                    (Type::Real, Type::Real)
                    | (Type::Real, Type::Matrix(1, 1))
                    | (Type::Matrix(1, 1), Type::Real) => target,
                    _ => return Err(TypeError::Invalid("unsupported cast operand types")),
                }
            }
            RawExpr::Binop(Binop::SingleSubscript, sequence, _) => {
                let Type::Seq(sequence) = node_type(sequence)? else {
                    return Err(TypeError::Invalid("subscripted expression is not a sequence"));
                };
                sequence.t
            }
            RawExpr::Binop(Binop::Power, base, _) => node_type(base)?,
            RawExpr::Binop(Binop::Div, left, right) => division_type(
                node_type(left)?,
                node_type(right)?,
            )?,
            RawExpr::Binop(_, left, right) => {
                numeric_lub(node_type(left)?, node_type(right)?)?
            }
            RawExpr::Triop(_, _, _, _) => {
                return Err(TypeError::Unsupported("ternary operator typing is unsupported"));
            }
            RawExpr::Finop(Finop::And | Finop::Or, expressions) => {
                for expression in expressions {
                    require_bool(node_type(expression)?)?;
                }
                Type::Bool
            }
            RawExpr::Finop(Finop::Plus, expressions) => {
                fold_types(expressions, add_type)?
            }
            RawExpr::Finop(Finop::Times, expressions) => {
                fold_types(expressions, multiply_type)?
            }
            RawExpr::Finop(_, _) => {
                return Err(TypeError::Unsupported("finite operator typing is unsupported"));
            }
            RawExpr::CmpChain(chain) => {
                let mut previous = node_type(&chain.start)?;
                for (_, current) in &chain.assertions {
                    comparable(&previous, &node_type(current)?)?;
                    previous = node_type(current)?;
                }
                Type::Bool
            }
            RawExpr::LogicChain(LogicChain { start, assertions }) => {
                require_bool(node_type(start)?)?;
                for (_, expression) in assertions {
                    require_bool(node_type(expression)?)?;
                }
                Type::Bool
            }
            RawExpr::Seqop(_, _, body) => node_type(body)?,
        };
        Ok(Some(ty))
    }

    fn infer_monop(&self, op: Monop, inner: Type) -> Result<Type, TypeError> {
        match op {
            Monop::Neg => require_numeric(inner),
            Monop::Transpose => match inner {
                Type::Matrix(rows, cols) => Ok(Type::Matrix(cols, rows)),
                _ => Err(TypeError::Invalid("transpose requires a matrix")),
            },
            Monop::Trace | Monop::Det => match inner {
                Type::Matrix(rows, cols) if rows == cols => Ok(Type::Real),
                Type::Matrix(_, _) => Err(TypeError::Invalid("operator requires a square matrix")),
                _ => Err(TypeError::Invalid("operator requires a matrix")),
            },
            Monop::Norm1 | Monop::Norm2 | Monop::NormInfty | Monop::NormFrob => Ok(Type::Real),
            Monop::Inverse => match inner {
                Type::Matrix(rows, cols) if rows == cols => Ok(Type::Matrix(rows, cols)),
                Type::Matrix(_, _) => Err(TypeError::Invalid("inverse requires a square matrix")),
                _ => Err(TypeError::Invalid("inverse requires a matrix")),
            },
        }
    }

    fn implicit_dimension(&self, dimension: crate::ImplicitDimension) -> Result<u64, TypeError> {
        self.environment
            .implicit_dimensions
            .get(&dimension)
            .copied()
            .ok_or(TypeError::Invalid("missing implicit matrix dimension"))
    }

    fn concrete_type_expr<Metadata>(&self, ty: &TypeExpr<Metadata>) -> Result<Type, TypeError> {
        match ty {
            TypeExpr::Bool => Ok(Type::Bool),
            TypeExpr::Nat => Ok(Type::Nat),
            TypeExpr::Int => Ok(Type::Int),
            TypeExpr::Real => Ok(Type::Real),
            TypeExpr::Matrix(rows, cols) => Ok(Type::Matrix(
                self.concrete_dimension(rows)?,
                self.concrete_dimension(cols)?,
            )),
            TypeExpr::Seq(element, size) => {
                let RawExpr::Type(element) = &element.raw else {
                    return Err(TypeError::Invalid("sequence element must be a type expression"));
                };
                Ok(Type::Seq(Box::new(SeqType {
                    t: self.concrete_type_expr(element)?,
                    n: self.concrete_dimension(size)?,
                })))
            }
        }
    }

    fn concrete_dimension<Metadata>(&self, expression: &Expr<Metadata>) -> Result<u64, TypeError> {
        if let RawExpr::NatLiteral(value) = expression.raw {
            return Ok(value);
        }
        self.environment
            .equalities
            .get(&expression.with_default_metadata())
            .copied()
            .ok_or(TypeError::Invalid("resolved type dimension is not concrete"))
    }
}

impl<Metadata: MaybeTyped> VisitMut<Metadata> for TypeResolver<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        {
            let raw = &mut node
                .get_mut()
                .expect("type resolution requires uniquely owned expressions")
                .raw;
            match raw {
                RawExpr::Hole
                | RawExpr::IdentityMatrix { .. }
                | RawExpr::ZeroMatrix { .. }
                | RawExpr::Variable(_)
                | RawExpr::NatLiteral(_) => {}
                RawExpr::StandardBasis { index, .. } => self.visit_expr_mut(context, index),
                RawExpr::Type(ty) => visit_type_children(self, context, ty),
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
                RawExpr::Binop(_, left, right) => {
                    self.visit_expr_mut(context, left);
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Triop(_, first, second, third) => {
                    self.visit_expr_mut(context, first);
                    self.visit_expr_mut(context, second);
                    self.visit_expr_mut(context, third);
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
                RawExpr::LogicChain(chain) => {
                    self.visit_expr_mut(context, &mut chain.start);
                    for (_, expression) in &mut chain.assertions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::Seqop(_, range, body) => {
                    self.visit_expr_mut(context, &mut range.from);
                    self.visit_expr_mut(context, &mut range.to);
                    let previous = self
                        .lexical_types
                        .insert(range.index_variable.clone(), Type::Nat);
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
        let inferred = self.infer(node);
        if let Some(Some(ty)) = self.record(inferred) {
            node.get_mut()
                .expect("type resolution requires uniquely owned expressions")
                .meta
                .put_type(type_expr(ty));
        }
    }
}

fn visit_type_children<Metadata: MaybeTyped>(
    resolver: &mut TypeResolver<'_>,
    context: VisitContext,
    ty: &mut TypeExpr<Metadata>,
) {
    match ty {
        TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
        TypeExpr::Matrix(first, second) | TypeExpr::Seq(first, second) => {
            resolver.visit_expr_mut(context, first);
            resolver.visit_expr_mut(context, second);
        }
    }
}

fn node_type<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> Result<Type, TypeError> {
    concrete_type_expr(&expression.meta.get_type()?)
}

pub(crate) fn type_expr(ty: Type) -> TypeExpr<()> {
    match ty {
        Type::Bool => TypeExpr::Bool,
        Type::Nat => TypeExpr::Nat,
        Type::Int => TypeExpr::Int,
        Type::Real => TypeExpr::Real,
        Type::Matrix(rows, cols) => TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows)),
            Expr::new(RawExpr::NatLiteral(cols)),
        ),
        Type::Seq(sequence) => TypeExpr::Seq(
            Expr::new(RawExpr::Type(type_expr(sequence.t))),
            Expr::new(RawExpr::NatLiteral(sequence.n)),
        ),
    }
}

pub(crate) fn concrete_type_expr<Metadata>(ty: &TypeExpr<Metadata>) -> Result<Type, TypeError> {
    match ty {
        TypeExpr::Bool => Ok(Type::Bool),
        TypeExpr::Nat => Ok(Type::Nat),
        TypeExpr::Int => Ok(Type::Int),
        TypeExpr::Real => Ok(Type::Real),
        TypeExpr::Matrix(rows, cols) => Ok(Type::Matrix(literal(rows)?, literal(cols)?)),
        TypeExpr::Seq(element, size) => {
            let RawExpr::Type(element) = &element.raw else {
                return Err(TypeError::Invalid("sequence element must be a type expression"));
            };
            Ok(Type::Seq(Box::new(SeqType {
                t: concrete_type_expr(element)?,
                n: literal(size)?,
            })))
        }
    }
}

fn literal<Metadata>(expression: &Expr<Metadata>) -> Result<u64, TypeError> {
    match expression.raw {
        RawExpr::NatLiteral(value) => Ok(value),
        _ => Err(TypeError::Invalid("resolved type dimension is not concrete")),
    }
}

fn fold_types<Metadata: MaybeTyped>(
    expressions: &[Expr<Metadata>],
    operation: fn(Type, Type) -> Result<Type, TypeError>,
) -> Result<Type, TypeError> {
    let mut expressions = expressions.iter();
    let first = expressions
        .next()
        .ok_or(TypeError::Invalid("finite operation is empty"))?;
    expressions.try_fold(node_type(first)?, |left, right| {
        operation(left, node_type(right)?)
    })
}

fn require_bool(ty: Type) -> Result<Type, TypeError> {
    if ty == Type::Bool {
        Ok(Type::Bool)
    } else {
        Err(TypeError::Invalid("logical operation requires Boolean operands"))
    }
}

fn require_numeric(ty: Type) -> Result<Type, TypeError> {
    match ty {
        Type::Nat | Type::Int | Type::Real | Type::Matrix(_, _) => Ok(ty),
        _ => Err(TypeError::Invalid("operation requires numeric operands")),
    }
}

fn numeric_lub(left: Type, right: Type) -> Result<Type, TypeError> {
    match (left, right) {
        (Type::Nat, Type::Nat) => Ok(Type::Nat),
        (Type::Nat | Type::Int, Type::Nat | Type::Int) => Ok(Type::Int),
        (Type::Nat | Type::Int | Type::Real, Type::Nat | Type::Int | Type::Real) => Ok(Type::Real),
        _ => Err(TypeError::Invalid("operation requires numeric scalar operands")),
    }
}

fn add_type(left: Type, right: Type) -> Result<Type, TypeError> {
    match (&left, &right) {
        (Type::Matrix(lr, lc), Type::Matrix(rr, rc)) if (lr, lc) == (rr, rc) => Ok(left),
        (Type::Matrix(_, _), Type::Matrix(_, _)) => {
            Err(TypeError::Invalid("matrix addition requires equal shapes"))
        }
        (Type::Matrix(_, _), _) | (_, Type::Matrix(_, _)) => {
            Err(TypeError::Invalid("matrix and scalar addition is unsupported"))
        }
        _ => numeric_lub(left, right),
    }
}

fn multiply_type(left: Type, right: Type) -> Result<Type, TypeError> {
    match (left, right) {
        (Type::Matrix(rows, inner), Type::Matrix(other_inner, cols)) if inner == other_inner => {
            Ok(Type::Matrix(rows, cols))
        }
        (Type::Matrix(_, _), Type::Matrix(_, _)) => Err(TypeError::Invalid(
            "matrix multiplication requires compatible dimensions",
        )),
        (matrix @ Type::Matrix(_, _), scalar) | (scalar, matrix @ Type::Matrix(_, _)) => {
            require_numeric(scalar)?;
            Ok(matrix)
        }
        (left, right) => numeric_lub(left, right),
    }
}

fn division_type(left: Type, right: Type) -> Result<Type, TypeError> {
    let scalar = |ty| match ty {
        Type::Matrix(1, 1) => Ok(Type::Real),
        Type::Matrix(_, _) => Err(TypeError::Invalid(
            "matrix division is only supported for 1x1 matrices",
        )),
        ty => Ok(ty),
    };
    numeric_lub(scalar(left)?, scalar(right)?)
}

fn comparable(left: &Type, right: &Type) -> Result<(), TypeError> {
    match (left, right) {
        (Type::Bool, _) | (_, Type::Bool) => {
            Err(TypeError::Invalid("Boolean comparisons are unsupported"))
        }
        (Type::Matrix(lr, lc), Type::Matrix(rr, rc)) if (lr, lc) == (rr, rc) => Ok(()),
        (Type::Matrix(_, _), Type::Matrix(_, _)) => {
            Err(TypeError::Invalid("matrix comparison requires equal shapes"))
        }
        (Type::Matrix(1, 1), Type::Nat | Type::Int | Type::Real)
        | (Type::Nat | Type::Int | Type::Real, Type::Matrix(1, 1)) => Ok(()),
        (Type::Matrix(_, _), _) | (_, Type::Matrix(_, _)) => {
            Err(TypeError::Invalid("matrix and scalar comparison is unsupported"))
        }
        _ => {
            numeric_lub(left.clone(), right.clone())?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ratex_parser::parse;

    use super::{MaybeTyped, TypeResolver, TypedMetadata};
    use crate::{
        Environment, Expr, RawExpr, SeqType, Type, TypeExpr, Variable, from_tex,
        visit_mut::VisitContext,
    };

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
    };

    fn resolve(environment: &Environment, tex: &str) -> Expr<TypedMetadata> {
        let parsed: Expr<()> = from_tex::expr(&parse(tex).unwrap()).unwrap();
        let mut expression = parsed.with_default_metadata();
        TypeResolver::new(environment)
            .resolve(&mut expression, POSITIVE)
            .unwrap();
        expression
    }

    #[test]
    fn resolves_promoted_compounds_and_preserves_one_by_one_matrices() {
        let environment = Environment {
            types: HashMap::from([
                (Variable::new("A"), Type::Matrix(1, 1)),
                (Variable::new("x"), Type::Real),
            ]),
            ..Environment::default()
        };
        let matrix = resolve(&environment, "A + A");
        assert!(matches!(
            matrix.meta.get_type().unwrap(),
            TypeExpr::Matrix(ref rows, ref cols)
                if matches!(rows.raw, RawExpr::NatLiteral(1))
                    && matches!(cols.raw, RawExpr::NatLiteral(1))
        ));
        assert_eq!(
            resolve(&environment, "x + 1").meta.get_type().unwrap(),
            TypeExpr::Real
        );
    }

    #[test]
    fn resolves_lexically_bound_sequence_indices() {
        let environment = Environment {
            types: HashMap::from([
                (
                    Variable::new("z"),
                    Type::Seq(Box::new(SeqType {
                        t: Type::Real,
                        n: 2,
                    })),
                ),
                (Variable::new("n"), Type::Nat),
            ]),
            equalities: HashMap::from([(
                Expr::new(RawExpr::Variable(Variable::new("n"))),
                2,
            )]),
            ..Environment::default()
        };
        assert_eq!(
            resolve(&environment, r"\sum_{i=1}^{n}z_i")
                .meta
                .get_type()
                .unwrap(),
            TypeExpr::Real
        );
    }
}
