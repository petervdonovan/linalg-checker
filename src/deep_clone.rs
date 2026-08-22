use crate::{CmpChain, Expr, LogicChain, Matrix, Range, RawExpr, TypeExpr};

pub(crate) fn deep_clone<Metadata: Clone>(expression: &Expr<Metadata>) -> Expr<Metadata> {
    let raw = match &expression.raw {
        RawExpr::Hole => RawExpr::Hole,
        RawExpr::ImplicitDimension(dimension) => RawExpr::ImplicitDimension(*dimension),
        RawExpr::IdentityMatrix { dimension } => RawExpr::IdentityMatrix {
            dimension: *dimension,
        },
        RawExpr::StandardBasis { index, dimension } => RawExpr::StandardBasis {
            index: deep_clone(index),
            dimension: *dimension,
        },
        RawExpr::ZeroMatrix { rows, cols } => RawExpr::ZeroMatrix {
            rows: *rows,
            cols: *cols,
        },
        RawExpr::Type(ty) => RawExpr::Type(deep_clone_type(ty)),
        RawExpr::Variable(variable) => RawExpr::Variable(variable.clone()),
        RawExpr::NatLiteral(value) => RawExpr::NatLiteral(*value),
        RawExpr::Matrix(matrix) => RawExpr::Matrix(Matrix {
            rows: matrix.rows,
            cols: matrix.cols,
            elements: matrix.elements.iter().map(deep_clone).collect(),
        }),
        RawExpr::Monop(op, inner) => RawExpr::Monop(*op, deep_clone(inner)),
        RawExpr::Binop(op, left, right) => RawExpr::Binop(*op, deep_clone(left), deep_clone(right)),
        RawExpr::Triop(op, first, second, third) => RawExpr::Triop(
            *op,
            deep_clone(first),
            deep_clone(second),
            deep_clone(third),
        ),
        RawExpr::Finop(op, expressions) => {
            RawExpr::Finop(*op, expressions.iter().map(deep_clone).collect())
        }
        RawExpr::CmpChain(chain) => RawExpr::CmpChain(CmpChain {
            start: deep_clone(&chain.start),
            assertions: chain
                .assertions
                .iter()
                .map(|(op, expression)| (*op, deep_clone(expression)))
                .collect(),
        }),
        RawExpr::LogicChain(chain) => RawExpr::LogicChain(LogicChain {
            start: deep_clone(&chain.start),
            assertions: chain
                .assertions
                .iter()
                .map(|(op, expression)| (*op, deep_clone(expression)))
                .collect(),
        }),
        RawExpr::Seqop(op, range, body) => RawExpr::Seqop(
            *op,
            Range {
                index_variable: range.index_variable.clone(),
                from: deep_clone(&range.from),
                to: deep_clone(&range.to),
            },
            deep_clone(body),
        ),
    };
    Expr::with_metadata(expression.meta.clone(), raw)
}

fn deep_clone_type<Metadata: Clone>(ty: &TypeExpr<Metadata>) -> TypeExpr<Metadata> {
    match ty {
        TypeExpr::Bool => TypeExpr::Bool,
        TypeExpr::Nat => TypeExpr::Nat,
        TypeExpr::Int => TypeExpr::Int,
        TypeExpr::Real => TypeExpr::Real,
        TypeExpr::Matrix(rows, cols) => TypeExpr::Matrix(deep_clone(rows), deep_clone(cols)),
        TypeExpr::Seq(element, size) => TypeExpr::Seq(deep_clone(element), deep_clone(size)),
    }
}
