//! Immutable expression-tree traversal.
//!
//! Trait methods delegate to public free walkers, following `syn::visit`.

use crate::{
    Binop, CmpChain, Expr, Finop, ImplicitDimension, LogicChain, Matrix, MetaExpr, Monop, Range,
    RawExpr, SeqOp, Triop, TypeExpr, Variable,
};

pub trait Visit<Metadata> {
    fn visit_expr(&mut self, node: &Expr<Metadata>) {
        visit_expr(self, node);
    }
    fn visit_meta_expr(&mut self, node: &MetaExpr<Metadata>) {
        visit_meta_expr(self, node);
    }
    fn visit_metadata(&mut self, node: &Metadata) {
        visit_metadata(self, node);
    }
    fn visit_raw_expr(&mut self, node: &RawExpr<Metadata>) {
        visit_raw_expr(self, node);
    }
    fn visit_type_expr(&mut self, node: &TypeExpr<Metadata>) {
        visit_type_expr(self, node);
    }
    fn visit_matrix(&mut self, node: &Matrix<Expr<Metadata>>) {
        visit_matrix(self, node);
    }
    fn visit_range(&mut self, node: &Range<Metadata>) {
        visit_range(self, node);
    }
    fn visit_cmp_chain(&mut self, node: &CmpChain<Metadata>) {
        visit_cmp_chain(self, node);
    }
    fn visit_logic_chain(&mut self, node: &LogicChain<Metadata>) {
        visit_logic_chain(self, node);
    }
    fn visit_variable(&mut self, node: &Variable) {
        visit_variable(self, node);
    }

    fn visit_raw_expr_hole(&mut self) {
        visit_raw_expr_hole(self);
    }
    fn visit_raw_expr_identity_matrix(&mut self, dimension: &ImplicitDimension) {
        visit_raw_expr_identity_matrix(self, dimension);
    }
    fn visit_raw_expr_standard_basis(
        &mut self,
        index: &Expr<Metadata>,
        dimension: &ImplicitDimension,
    ) {
        visit_raw_expr_standard_basis(self, index, dimension);
    }
    fn visit_raw_expr_zero_matrix(&mut self, rows: &ImplicitDimension, cols: &ImplicitDimension) {
        visit_raw_expr_zero_matrix(self, rows, cols);
    }
    fn visit_raw_expr_type(&mut self, ty: &TypeExpr<Metadata>) {
        visit_raw_expr_type(self, ty);
    }
    fn visit_raw_expr_variable(&mut self, variable: &Variable) {
        visit_raw_expr_variable(self, variable);
    }
    fn visit_raw_expr_nat_literal(&mut self, value: &u64) {
        visit_raw_expr_nat_literal(self, value);
    }
    fn visit_raw_expr_matrix(&mut self, matrix: &Matrix<Expr<Metadata>>) {
        visit_raw_expr_matrix(self, matrix);
    }
    fn visit_raw_expr_monop(&mut self, op: &Monop, expression: &Expr<Metadata>) {
        visit_raw_expr_monop(self, op, expression);
    }
    fn visit_raw_expr_binop(&mut self, op: &Binop, left: &Expr<Metadata>, right: &Expr<Metadata>) {
        visit_raw_expr_binop(self, op, left, right);
    }
    fn visit_raw_expr_triop(
        &mut self,
        op: &Triop,
        first: &Expr<Metadata>,
        second: &Expr<Metadata>,
        third: &Expr<Metadata>,
    ) {
        visit_raw_expr_triop(self, op, first, second, third);
    }
    fn visit_raw_expr_finop(&mut self, op: &Finop, expressions: &[Expr<Metadata>]) {
        visit_raw_expr_finop(self, op, expressions);
    }
    fn visit_raw_expr_cmp_chain(&mut self, chain: &CmpChain<Metadata>) {
        visit_raw_expr_cmp_chain(self, chain);
    }
    fn visit_raw_expr_logic_chain(&mut self, chain: &LogicChain<Metadata>) {
        visit_raw_expr_logic_chain(self, chain);
    }
    fn visit_raw_expr_seqop(&mut self, op: &SeqOp, range: &Range<Metadata>, body: &Expr<Metadata>) {
        visit_raw_expr_seqop(self, op, range, body);
    }
}

pub fn visit_expr<V: Visit<M> + ?Sized, M>(v: &mut V, n: &Expr<M>) {
    v.visit_meta_expr(n);
}
pub fn visit_meta_expr<V: Visit<M> + ?Sized, M>(v: &mut V, n: &MetaExpr<M>) {
    v.visit_metadata(&n.meta);
    v.visit_raw_expr(&n.raw);
}
pub fn visit_metadata<V: Visit<M> + ?Sized, M>(_v: &mut V, _n: &M) {}
pub fn visit_raw_expr<V: Visit<M> + ?Sized, M>(v: &mut V, n: &RawExpr<M>) {
    match n {
        RawExpr::Hole => v.visit_raw_expr_hole(),
        RawExpr::IdentityMatrix { dimension } => v.visit_raw_expr_identity_matrix(dimension),
        RawExpr::StandardBasis { index, dimension } => {
            v.visit_raw_expr_standard_basis(index, dimension)
        }
        RawExpr::ZeroMatrix { rows, cols } => v.visit_raw_expr_zero_matrix(rows, cols),
        RawExpr::Type(ty) => v.visit_raw_expr_type(ty),
        RawExpr::Variable(variable) => v.visit_raw_expr_variable(variable),
        RawExpr::NatLiteral(value) => v.visit_raw_expr_nat_literal(value),
        RawExpr::Matrix(matrix) => v.visit_raw_expr_matrix(matrix),
        RawExpr::Monop(op, expression) => v.visit_raw_expr_monop(op, expression),
        RawExpr::Binop(op, left, right) => v.visit_raw_expr_binop(op, left, right),
        RawExpr::Triop(op, first, second, third) => {
            v.visit_raw_expr_triop(op, first, second, third)
        }
        RawExpr::Finop(op, expressions) => v.visit_raw_expr_finop(op, expressions),
        RawExpr::CmpChain(chain) => v.visit_raw_expr_cmp_chain(chain),
        RawExpr::LogicChain(chain) => v.visit_raw_expr_logic_chain(chain),
        RawExpr::Seqop(op, range, body) => v.visit_raw_expr_seqop(op, range, body),
    }
}
pub fn visit_type_expr<V: Visit<M> + ?Sized, M>(v: &mut V, n: &TypeExpr<M>) {
    match n {
        TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
        TypeExpr::Matrix(a, b) | TypeExpr::Seq(a, b) => {
            v.visit_expr(a);
            v.visit_expr(b);
        }
    }
}
pub fn visit_matrix<V: Visit<M> + ?Sized, M>(v: &mut V, n: &Matrix<Expr<M>>) {
    for e in &n.elements {
        v.visit_expr(e);
    }
}
pub fn visit_range<V: Visit<M> + ?Sized, M>(v: &mut V, n: &Range<M>) {
    v.visit_variable(&n.index_variable);
    v.visit_expr(&n.from);
    v.visit_expr(&n.to);
}
pub fn visit_cmp_chain<V: Visit<M> + ?Sized, M>(v: &mut V, n: &CmpChain<M>) {
    v.visit_expr(&n.start);
    for (_, e) in &n.assertions {
        v.visit_expr(e);
    }
}
/// Unlike polarity-aware mutation, immutable traversal visits every stored
/// logic-chain expression exactly once, including multi-edge chains and Iff.
pub fn visit_logic_chain<V: Visit<M> + ?Sized, M>(v: &mut V, n: &LogicChain<M>) {
    v.visit_expr(&n.start);
    for (_, e) in &n.assertions {
        v.visit_expr(e);
    }
}
pub fn visit_variable<V: Visit<M> + ?Sized, M>(_v: &mut V, _n: &Variable) {}
pub fn visit_raw_expr_hole<V: Visit<M> + ?Sized, M>(_v: &mut V) {}
pub fn visit_raw_expr_identity_matrix<V: Visit<M> + ?Sized, M>(_v: &mut V, _d: &ImplicitDimension) {
}
pub fn visit_raw_expr_standard_basis<V: Visit<M> + ?Sized, M>(
    v: &mut V,
    i: &Expr<M>,
    _d: &ImplicitDimension,
) {
    v.visit_expr(i);
}
pub fn visit_raw_expr_zero_matrix<V: Visit<M> + ?Sized, M>(
    _v: &mut V,
    _r: &ImplicitDimension,
    _c: &ImplicitDimension,
) {
}
pub fn visit_raw_expr_type<V: Visit<M> + ?Sized, M>(v: &mut V, t: &TypeExpr<M>) {
    v.visit_type_expr(t);
}
pub fn visit_raw_expr_variable<V: Visit<M> + ?Sized, M>(v: &mut V, n: &Variable) {
    v.visit_variable(n);
}
pub fn visit_raw_expr_nat_literal<V: Visit<M> + ?Sized, M>(_v: &mut V, _n: &u64) {}
pub fn visit_raw_expr_matrix<V: Visit<M> + ?Sized, M>(v: &mut V, n: &Matrix<Expr<M>>) {
    v.visit_matrix(n);
}
pub fn visit_raw_expr_monop<V: Visit<M> + ?Sized, M>(v: &mut V, _op: &Monop, e: &Expr<M>) {
    v.visit_expr(e);
}
pub fn visit_raw_expr_binop<V: Visit<M> + ?Sized, M>(
    v: &mut V,
    _op: &Binop,
    a: &Expr<M>,
    b: &Expr<M>,
) {
    v.visit_expr(a);
    v.visit_expr(b);
}
pub fn visit_raw_expr_triop<V: Visit<M> + ?Sized, M>(
    v: &mut V,
    _op: &Triop,
    a: &Expr<M>,
    b: &Expr<M>,
    c: &Expr<M>,
) {
    v.visit_expr(a);
    v.visit_expr(b);
    v.visit_expr(c);
}
pub fn visit_raw_expr_finop<V: Visit<M> + ?Sized, M>(v: &mut V, _op: &Finop, es: &[Expr<M>]) {
    for e in es {
        v.visit_expr(e);
    }
}
pub fn visit_raw_expr_cmp_chain<V: Visit<M> + ?Sized, M>(v: &mut V, n: &CmpChain<M>) {
    v.visit_cmp_chain(n);
}
pub fn visit_raw_expr_logic_chain<V: Visit<M> + ?Sized, M>(v: &mut V, n: &LogicChain<M>) {
    v.visit_logic_chain(n);
}
pub fn visit_raw_expr_seqop<V: Visit<M> + ?Sized, M>(
    v: &mut V,
    _op: &SeqOp,
    r: &Range<M>,
    b: &Expr<M>,
) {
    v.visit_range(r);
    v.visit_expr(b);
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::Visit;
    use crate::{
        Binop, Cmp, CmpChain, Expr, Finop, ImplicitDimension, Logic, LogicChain, Matrix, Monop,
        Range, RawExpr, SeqOp, Triop, TypeExpr, Variable,
    };
    struct Variables(Vec<String>);
    impl Visit<()> for Variables {
        fn visit_variable(&mut self, v: &Variable) {
            self.0.push(v.name.clone());
        }
    }
    #[test]
    fn visits_every_logic_chain_expression_once() {
        let v = |n| Expr::new(RawExpr::Variable(Variable::new(n)));
        let e = Expr::new(RawExpr::LogicChain(LogicChain {
            start: v("P"),
            assertions: vec![(Logic::Iff, v("Q")), (Logic::Imp, v("R"))],
        }));
        let mut visitor = Variables(Vec::new());
        visitor.visit_expr(&e);
        assert_eq!(visitor.0, ["P", "Q", "R"]);
    }

    #[test]
    fn every_raw_expression_variant_has_an_immutable_hook() {
        struct Variants(BTreeSet<&'static str>);
        impl Visit<()> for Variants {
            fn visit_raw_expr(&mut self, node: &RawExpr<()>) {
                self.0.insert(match node {
                    RawExpr::Hole => "hole",
                    RawExpr::IdentityMatrix { .. } => "identity",
                    RawExpr::StandardBasis { .. } => "basis",
                    RawExpr::ZeroMatrix { .. } => "zero",
                    RawExpr::Type(_) => "type",
                    RawExpr::Variable(_) => "variable",
                    RawExpr::NatLiteral(_) => "literal",
                    RawExpr::Matrix(_) => "matrix",
                    RawExpr::Monop(_, _) => "monop",
                    RawExpr::Binop(_, _, _) => "binop",
                    RawExpr::Triop(_, _, _, _) => "triop",
                    RawExpr::Finop(_, _) => "finop",
                    RawExpr::CmpChain(_) => "comparison",
                    RawExpr::LogicChain(_) => "logic",
                    RawExpr::Seqop(_, _, _) => "sequence",
                });
                super::visit_raw_expr(self, node);
            }
        }
        let d = ImplicitDimension::fresh();
        let literal = || Expr::new(RawExpr::NatLiteral(1));
        let expressions = vec![
            Expr::new(RawExpr::Hole),
            Expr::new(RawExpr::IdentityMatrix { dimension: d }),
            Expr::new(RawExpr::StandardBasis {
                index: literal(),
                dimension: d,
            }),
            Expr::new(RawExpr::ZeroMatrix { rows: d, cols: d }),
            Expr::new(RawExpr::Type(TypeExpr::Matrix(literal(), literal()))),
            Expr::new(RawExpr::Variable(Variable::new("x"))),
            literal(),
            Expr::new(RawExpr::Matrix(Matrix {
                rows: 1,
                cols: 1,
                elements: vec![literal()],
            })),
            Expr::new(RawExpr::Monop(Monop::Neg, literal())),
            Expr::new(RawExpr::Binop(Binop::Power, literal(), literal())),
            Expr::new(RawExpr::Triop(
                Triop::DoubleSubscript,
                literal(),
                literal(),
                literal(),
            )),
            Expr::new(RawExpr::Finop(Finop::Plus, vec![literal()])),
            Expr::new(RawExpr::CmpChain(CmpChain {
                start: literal(),
                assertions: vec![(Cmp::Eq, literal())],
            })),
            Expr::new(RawExpr::LogicChain(LogicChain {
                start: literal(),
                assertions: vec![(Logic::Imp, literal())],
            })),
            Expr::new(RawExpr::Seqop(
                SeqOp::Sum,
                Range {
                    index_variable: Variable::new("i"),
                    from: literal(),
                    to: literal(),
                },
                literal(),
            )),
        ];
        let mut visitor = Variants(BTreeSet::new());
        for expression in &expressions {
            visitor.visit_expr(expression);
        }
        assert_eq!(visitor.0.len(), 15);
    }
}
