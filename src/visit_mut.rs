//! Mutable expression-tree traversal with logical-polarity context.
//!
//! The API follows the structure of `syn::visit_mut`: trait methods delegate to
//! public free functions, so an override can perform custom work and then call
//! the corresponding free function to continue the default traversal.

use crate::{
    Binop, CmpChain, Expr, Finop, ImplicitDimension, Logic, LogicChain, Matrix, MetaExpr, Monop,
    Range, RawExpr, SeqOp, Triop, TypeExpr, Variable,
};

#[derive(Clone, Debug)]
pub enum Existence<Metadata> {
    Guaranteed,
    Checkable(Vec<Expr<Metadata>>),
    Assumed,
}

#[derive(Clone, Debug)]
pub struct SideCondition<Metadata> {
    pub introduced_variable: Variable,
    pub display_name: String,
    pub introduced_type: TypeExpr<()>,
    pub defining_assertions: Vec<Expr<Metadata>>,
    pub existence: Existence<Metadata>,
}

/// Context inherited while traversing an expression tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VisitContext {
    /// Whether the surrounding Boolean expression is monotone increasing in
    /// the truth of the atomic sentence currently being visited.
    ///
    /// `false` means the surrounding expression is monotone decreasing in that
    /// truth value. Negation and the antecedent of an implication reverse this
    /// polarity.
    pub logical_polarity: bool,
}

impl VisitContext {
    fn flipped(self) -> Self {
        Self {
            logical_polarity: !self.logical_polarity,
        }
    }
}

/// Mutable traversal of an expression tree.
///
/// The default implementation expects every visited [`Expr`] to be uniquely
/// owned. It panics if the expression's internal `Rc` is shared.
pub trait VisitMut<Metadata> {
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        vec![]
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        visit_expr_mut(self, context, node);
    }

    fn visit_meta_expr_mut(&mut self, context: VisitContext, node: &mut MetaExpr<Metadata>) {
        visit_meta_expr_mut(self, context, node);
    }

    fn visit_metadata_mut(&mut self, context: VisitContext, metadata: &mut Metadata) {
        visit_metadata_mut(self, context, metadata);
    }

    fn visit_raw_expr_mut(&mut self, context: VisitContext, node: &mut RawExpr<Metadata>) {
        visit_raw_expr_mut(self, context, node);
    }

    fn visit_type_expr_mut(&mut self, context: VisitContext, node: &mut TypeExpr<Metadata>) {
        visit_type_expr_mut(self, context, node);
    }

    fn visit_matrix_mut(&mut self, context: VisitContext, node: &mut Matrix<Expr<Metadata>>) {
        visit_matrix_mut(self, context, node);
    }

    fn visit_range_mut(&mut self, context: VisitContext, node: &mut Range<Metadata>) {
        visit_range_mut(self, context, node);
    }

    fn visit_cmp_chain_mut(&mut self, context: VisitContext, node: &mut CmpChain<Metadata>) {
        visit_cmp_chain_mut(self, context, node);
    }

    fn visit_logic_chain_mut(&mut self, context: VisitContext, node: &mut LogicChain<Metadata>) {
        visit_logic_chain_mut(self, context, node);
    }

    fn visit_variable_mut(&mut self, context: VisitContext, node: &mut Variable) {
        visit_variable_mut(self, context, node);
    }

    fn visit_raw_expr_hole_mut(&mut self, context: VisitContext) {
        visit_raw_expr_hole_mut(self, context);
    }

    fn visit_raw_expr_identity_matrix_mut(
        &mut self,
        context: VisitContext,
        dimension: &mut ImplicitDimension,
    ) {
        visit_raw_expr_identity_matrix_mut(self, context, dimension);
    }

    fn visit_raw_expr_standard_basis_mut(
        &mut self,
        context: VisitContext,
        index: &mut Expr<Metadata>,
        dimension: &mut ImplicitDimension,
    ) {
        visit_raw_expr_standard_basis_mut(self, context, index, dimension);
    }

    fn visit_raw_expr_zero_matrix_mut(
        &mut self,
        context: VisitContext,
        rows: &mut ImplicitDimension,
        cols: &mut ImplicitDimension,
    ) {
        visit_raw_expr_zero_matrix_mut(self, context, rows, cols);
    }

    fn visit_raw_expr_type_mut(&mut self, context: VisitContext, ty: &mut TypeExpr<Metadata>) {
        visit_raw_expr_type_mut(self, context, ty);
    }

    fn visit_raw_expr_variable_mut(&mut self, context: VisitContext, variable: &mut Variable) {
        visit_raw_expr_variable_mut(self, context, variable);
    }

    fn visit_raw_expr_nat_literal_mut(&mut self, context: VisitContext, value: &mut u64) {
        visit_raw_expr_nat_literal_mut(self, context, value);
    }

    fn visit_raw_expr_matrix_mut(
        &mut self,
        context: VisitContext,
        matrix: &mut Matrix<Expr<Metadata>>,
    ) {
        visit_raw_expr_matrix_mut(self, context, matrix);
    }

    fn visit_raw_expr_monop_mut(
        &mut self,
        context: VisitContext,
        op: &mut Monop,
        expression: &mut Expr<Metadata>,
    ) {
        visit_raw_expr_monop_mut(self, context, op, expression);
    }

    fn visit_raw_expr_binop_mut(
        &mut self,
        context: VisitContext,
        op: &mut Binop,
        left: &mut Expr<Metadata>,
        right: &mut Expr<Metadata>,
    ) {
        visit_raw_expr_binop_mut(self, context, op, left, right);
    }

    fn visit_raw_expr_triop_mut(
        &mut self,
        context: VisitContext,
        op: &mut Triop,
        first: &mut Expr<Metadata>,
        second: &mut Expr<Metadata>,
        third: &mut Expr<Metadata>,
    ) {
        visit_raw_expr_triop_mut(self, context, op, first, second, third);
    }

    fn visit_raw_expr_finop_mut(
        &mut self,
        context: VisitContext,
        op: &mut Finop,
        expressions: &mut Vec<Expr<Metadata>>,
    ) {
        visit_raw_expr_finop_mut(self, context, op, expressions);
    }

    fn visit_raw_expr_cmp_chain_mut(
        &mut self,
        context: VisitContext,
        chain: &mut CmpChain<Metadata>,
    ) {
        visit_raw_expr_cmp_chain_mut(self, context, chain);
    }

    fn visit_raw_expr_logic_chain_mut(
        &mut self,
        context: VisitContext,
        chain: &mut LogicChain<Metadata>,
    ) {
        visit_raw_expr_logic_chain_mut(self, context, chain);
    }

    fn visit_raw_expr_seqop_mut(
        &mut self,
        context: VisitContext,
        op: &mut SeqOp,
        range: &mut Range<Metadata>,
        body: &mut Expr<Metadata>,
    ) {
        visit_raw_expr_seqop_mut(self, context, op, range, body);
    }
}

pub fn visit_expr_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut Expr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_meta_expr_mut(
        context,
        node.get_mut()
            .expect("mutable expression visitors require uniquely owned expressions"),
    );
}

pub fn visit_meta_expr_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut MetaExpr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_metadata_mut(context, &mut node.meta);
    visitor.visit_raw_expr_mut(context, &mut node.raw);
}

pub fn visit_metadata_mut<V, Metadata>(
    _visitor: &mut V,
    _context: VisitContext,
    _metadata: &mut Metadata,
) where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut RawExpr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    match node {
        RawExpr::Hole => visitor.visit_raw_expr_hole_mut(context),
        RawExpr::IdentityMatrix { dimension } => {
            visitor.visit_raw_expr_identity_matrix_mut(context, dimension)
        }
        RawExpr::StandardBasis { index, dimension } => {
            visitor.visit_raw_expr_standard_basis_mut(context, index, dimension)
        }
        RawExpr::ZeroMatrix { rows, cols } => {
            visitor.visit_raw_expr_zero_matrix_mut(context, rows, cols)
        }
        RawExpr::Type(ty) => visitor.visit_raw_expr_type_mut(context, ty),
        RawExpr::Variable(variable) => visitor.visit_raw_expr_variable_mut(context, variable),
        RawExpr::NatLiteral(value) => visitor.visit_raw_expr_nat_literal_mut(context, value),
        RawExpr::Matrix(matrix) => visitor.visit_raw_expr_matrix_mut(context, matrix),
        RawExpr::Monop(op, expression) => visitor.visit_raw_expr_monop_mut(context, op, expression),
        RawExpr::Binop(op, left, right) => {
            visitor.visit_raw_expr_binop_mut(context, op, left, right)
        }
        RawExpr::Triop(op, first, second, third) => {
            visitor.visit_raw_expr_triop_mut(context, op, first, second, third)
        }
        RawExpr::Finop(op, expressions) => {
            visitor.visit_raw_expr_finop_mut(context, op, expressions)
        }
        RawExpr::CmpChain(chain) => visitor.visit_raw_expr_cmp_chain_mut(context, chain),
        RawExpr::LogicChain(chain) => visitor.visit_raw_expr_logic_chain_mut(context, chain),
        RawExpr::Seqop(op, range, body) => {
            visitor.visit_raw_expr_seqop_mut(context, op, range, body)
        }
    }
}

pub fn visit_type_expr_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut TypeExpr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    match node {
        TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
        TypeExpr::Matrix(rows, cols) | TypeExpr::Seq(rows, cols) => {
            visitor.visit_expr_mut(context, rows);
            visitor.visit_expr_mut(context, cols);
        }
    }
}

pub fn visit_matrix_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut Matrix<Expr<Metadata>>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    for element in &mut node.elements {
        visitor.visit_expr_mut(context, element);
    }
}

pub fn visit_range_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut Range<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_variable_mut(context, &mut node.index_variable);
    visitor.visit_expr_mut(context, &mut node.from);
    visitor.visit_expr_mut(context, &mut node.to);
}

pub fn visit_cmp_chain_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut CmpChain<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_expr_mut(context, &mut node.start);
    for (_, expression) in &mut node.assertions {
        visitor.visit_expr_mut(context, expression);
    }
}

/// Visits a compact logic chain according to its adjacency semantics.
///
/// `P implies Q implies R` means `(P implies Q) and (Q implies R)`, not
/// associative implication and not an assertion that `P` is true. The stored
/// `Q` therefore has both positive and negative occurrences. Until the context
/// can represent mixed polarity, chains with more than one implication panic.
/// Biconditional is likewise nonmonotone and currently unsupported.
pub fn visit_logic_chain_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    node: &mut LogicChain<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    assert!(
        node.assertions.len() <= 1,
        "mutable polarity traversal does not support multi-implication logic chains"
    );
    assert!(
        !node
            .assertions
            .iter()
            .any(|(op, _)| matches!(op, Logic::Iff)),
        "mutable polarity traversal does not support biconditional"
    );

    let Some((Logic::Imp, consequent)) = node.assertions.first_mut() else {
        visitor.visit_expr_mut(context, &mut node.start);
        return;
    };
    visitor.visit_expr_mut(context.flipped(), &mut node.start);
    visitor.visit_expr_mut(context, consequent);
}

pub fn visit_variable_mut<V, Metadata>(
    _visitor: &mut V,
    _context: VisitContext,
    _node: &mut Variable,
) where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_hole_mut<V, Metadata>(_visitor: &mut V, _context: VisitContext)
where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_identity_matrix_mut<V, Metadata>(
    _visitor: &mut V,
    _context: VisitContext,
    _dimension: &mut ImplicitDimension,
) where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_standard_basis_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    index: &mut Expr<Metadata>,
    _dimension: &mut ImplicitDimension,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_expr_mut(context, index);
}

pub fn visit_raw_expr_zero_matrix_mut<V, Metadata>(
    _visitor: &mut V,
    _context: VisitContext,
    _rows: &mut ImplicitDimension,
    _cols: &mut ImplicitDimension,
) where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_type_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    ty: &mut TypeExpr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_type_expr_mut(context, ty);
}

pub fn visit_raw_expr_variable_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    variable: &mut Variable,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_variable_mut(context, variable);
}

pub fn visit_raw_expr_nat_literal_mut<V, Metadata>(
    _visitor: &mut V,
    _context: VisitContext,
    _value: &mut u64,
) where
    V: VisitMut<Metadata> + ?Sized,
{
}

pub fn visit_raw_expr_matrix_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    matrix: &mut Matrix<Expr<Metadata>>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_matrix_mut(context, matrix);
}

pub fn visit_raw_expr_monop_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    op: &mut Monop,
    expression: &mut Expr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    let child_context = if matches!(op, Monop::Neg) {
        context.flipped()
    } else {
        context
    };
    visitor.visit_expr_mut(child_context, expression);
}

pub fn visit_raw_expr_binop_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    _op: &mut Binop,
    left: &mut Expr<Metadata>,
    right: &mut Expr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_expr_mut(context, left);
    visitor.visit_expr_mut(context, right);
}

pub fn visit_raw_expr_triop_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    _op: &mut Triop,
    first: &mut Expr<Metadata>,
    second: &mut Expr<Metadata>,
    third: &mut Expr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_expr_mut(context, first);
    visitor.visit_expr_mut(context, second);
    visitor.visit_expr_mut(context, third);
}

pub fn visit_raw_expr_finop_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    _op: &mut Finop,
    expressions: &mut Vec<Expr<Metadata>>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    for expression in expressions {
        visitor.visit_expr_mut(context, expression);
    }
}

pub fn visit_raw_expr_cmp_chain_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    chain: &mut CmpChain<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_cmp_chain_mut(context, chain);
}

pub fn visit_raw_expr_logic_chain_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    chain: &mut LogicChain<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_logic_chain_mut(context, chain);
}

pub fn visit_raw_expr_seqop_mut<V, Metadata>(
    visitor: &mut V,
    context: VisitContext,
    _op: &mut SeqOp,
    range: &mut Range<Metadata>,
    body: &mut Expr<Metadata>,
) where
    V: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_range_mut(context, range);
    visitor.visit_expr_mut(context, body);
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        panic::{AssertUnwindSafe, catch_unwind},
    };

    use super::{VisitContext, VisitMut};
    use crate::{
        Binop, Cmp, CmpChain, Expr, Finop, ImplicitDimension, Logic, LogicChain, Matrix, Monop,
        Range, RawExpr, SeqOp, Triop, TypeExpr, Variable,
    };

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
    };

    fn variable(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    struct PolarityRecorder {
        visits: Vec<(String, bool)>,
    }

    impl VisitMut<()> for PolarityRecorder {
        fn visit_variable_mut(&mut self, context: VisitContext, variable: &mut Variable) {
            self.visits
                .push((variable.name.clone(), context.logical_polarity));
        }
    }

    #[test]
    fn negation_flips_logical_polarity() {
        let mut expression = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                variable("x"),
                Expr::new(RawExpr::Monop(Monop::Neg, variable("y"))),
                Expr::new(RawExpr::Monop(
                    Monop::Neg,
                    Expr::new(RawExpr::Monop(Monop::Neg, variable("z"))),
                )),
            ],
        ));
        let mut visitor = PolarityRecorder { visits: Vec::new() };
        visitor.visit_expr_mut(POSITIVE, &mut expression);
        assert_eq!(
            visitor.visits,
            [("x".into(), true), ("y".into(), false), ("z".into(), true)]
        );
    }

    #[test]
    fn an_explicitly_negative_root_reverses_all_polarities() {
        let mut expression = Expr::new(RawExpr::Monop(Monop::Neg, variable("x")));
        let mut visitor = PolarityRecorder { visits: Vec::new() };
        visitor.visit_expr_mut(
            VisitContext {
                logical_polarity: false,
            },
            &mut expression,
        );
        assert_eq!(visitor.visits, [("x".into(), true)]);
    }

    #[test]
    fn variables_can_be_mutated_by_polarity() {
        struct RenameNegative;

        impl VisitMut<()> for RenameNegative {
            fn visit_variable_mut(&mut self, context: VisitContext, variable: &mut Variable) {
                if !context.logical_polarity {
                    variable.name.push_str("_negative");
                }
            }
        }

        let mut expression = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                variable("x"),
                Expr::new(RawExpr::Monop(Monop::Neg, variable("y"))),
            ],
        ));
        RenameNegative.visit_expr_mut(POSITIVE, &mut expression);
        assert_eq!(expression.as_latex().to_string(), "x - y_negative");
    }

    #[test]
    fn a_single_implication_flips_only_its_antecedent() {
        let mut expression = Expr::new(RawExpr::LogicChain(LogicChain {
            start: variable("P"),
            assertions: vec![(Logic::Imp, variable("Q"))],
        }));
        let mut visitor = PolarityRecorder { visits: Vec::new() };
        visitor.visit_expr_mut(POSITIVE, &mut expression);
        assert_eq!(visitor.visits, [("P".into(), false), ("Q".into(), true)]);
    }

    #[test]
    fn unsupported_logic_chains_panic_before_visiting_children() {
        for assertions in [
            vec![(Logic::Iff, variable("Q"))],
            vec![(Logic::Imp, variable("Q")), (Logic::Imp, variable("R"))],
        ] {
            let mut expression = Expr::new(RawExpr::LogicChain(LogicChain {
                start: variable("P"),
                assertions,
            }));
            let mut visitor = PolarityRecorder { visits: Vec::new() };
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    visitor.visit_expr_mut(POSITIVE, &mut expression);
                }))
                .is_err()
            );
            assert!(visitor.visits.is_empty());
        }
    }

    #[test]
    fn unary_hook_can_mutate_the_operator_and_delegate() {
        struct ReplaceWithNeg {
            visits: Vec<(String, bool)>,
        }

        impl VisitMut<()> for ReplaceWithNeg {
            fn visit_raw_expr_monop_mut(
                &mut self,
                context: VisitContext,
                op: &mut Monop,
                expression: &mut Expr<()>,
            ) {
                *op = Monop::Neg;
                super::visit_raw_expr_monop_mut(self, context, op, expression);
            }

            fn visit_variable_mut(&mut self, context: VisitContext, variable: &mut Variable) {
                self.visits
                    .push((variable.name.clone(), context.logical_polarity));
            }
        }

        let mut expression = Expr::new(RawExpr::Monop(Monop::Inverse, variable("x")));
        let mut visitor = ReplaceWithNeg { visits: Vec::new() };
        visitor.visit_expr_mut(POSITIVE, &mut expression);
        assert!(matches!(expression.raw, RawExpr::Monop(Monop::Neg, _)));
        assert_eq!(visitor.visits, [("x".into(), false)]);
    }

    #[test]
    fn metadata_is_mutable() {
        struct IncrementMetadata;

        impl VisitMut<u64> for IncrementMetadata {
            fn visit_metadata_mut(&mut self, _context: VisitContext, metadata: &mut u64) {
                *metadata += 1;
            }
        }

        let mut expression = Expr::with_metadata(
            1,
            RawExpr::Monop(Monop::Neg, Expr::with_metadata(2, RawExpr::NatLiteral(0))),
        );
        IncrementMetadata.visit_expr_mut(POSITIVE, &mut expression);
        assert_eq!(expression.meta, 2);
        let RawExpr::Monop(_, inner) = &expression.raw else {
            panic!("expected unary expression")
        };
        assert_eq!(inner.meta, 3);
    }

    #[test]
    fn every_raw_expression_variant_is_traversed() {
        struct VariantRecorder {
            variants: BTreeSet<&'static str>,
        }

        impl VisitMut<()> for VariantRecorder {
            fn visit_raw_expr_mut(&mut self, context: VisitContext, node: &mut RawExpr<()>) {
                self.variants.insert(match node {
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
                    RawExpr::CmpChain(_) => "cmp_chain",
                    RawExpr::LogicChain(_) => "logic_chain",
                    RawExpr::Seqop(_, _, _) => "seqop",
                });
                super::visit_raw_expr_mut(self, context, node);
            }
        }

        let dimension = ImplicitDimension::fresh();
        let mut expressions = vec![
            Expr::new(RawExpr::Hole),
            Expr::new(RawExpr::IdentityMatrix { dimension }),
            Expr::new(RawExpr::StandardBasis {
                index: Expr::new(RawExpr::NatLiteral(1)),
                dimension,
            }),
            Expr::new(RawExpr::ZeroMatrix {
                rows: dimension,
                cols: dimension,
            }),
            Expr::new(RawExpr::Type(TypeExpr::Seq(
                Expr::new(RawExpr::Type(TypeExpr::Matrix(
                    Expr::new(RawExpr::NatLiteral(2)),
                    Expr::new(RawExpr::NatLiteral(1)),
                ))),
                Expr::new(RawExpr::NatLiteral(3)),
            ))),
            variable("x"),
            Expr::new(RawExpr::NatLiteral(0)),
            Expr::new(RawExpr::Matrix(Matrix {
                rows: 1,
                cols: 1,
                elements: vec![variable("a")],
            })),
            Expr::new(RawExpr::Monop(Monop::Transpose, variable("A"))),
            Expr::new(RawExpr::Binop(Binop::Power, variable("x"), variable("n"))),
            Expr::new(RawExpr::Triop(
                Triop::DoubleSubscript,
                variable("A"),
                variable("i"),
                variable("j"),
            )),
            Expr::new(RawExpr::Finop(
                Finop::Times,
                vec![variable("x"), variable("y")],
            )),
            Expr::new(RawExpr::CmpChain(CmpChain {
                start: variable("x"),
                assertions: vec![(Cmp::Eq, variable("y"))],
            })),
            Expr::new(RawExpr::LogicChain(LogicChain {
                start: variable("P"),
                assertions: Vec::new(),
            })),
            Expr::new(RawExpr::Seqop(
                SeqOp::Sum,
                Range {
                    index_variable: Variable::new("i"),
                    from: Expr::new(RawExpr::NatLiteral(1)),
                    to: variable("n"),
                },
                variable("x"),
            )),
        ];
        let mut visitor = VariantRecorder {
            variants: BTreeSet::new(),
        };
        for expression in &mut expressions {
            visitor.visit_expr_mut(POSITIVE, expression);
        }
        assert_eq!(visitor.variants.len(), 15);
    }
}
