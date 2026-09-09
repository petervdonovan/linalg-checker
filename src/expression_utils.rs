use std::{cmp::Ordering, collections::BTreeSet};

use crate::{
    Expr, LogicChain, RawExpr, Variable,
    deep_clone::deep_clone,
    visit::{self, Visit},
    visit_mut::{self, VisitContext, VisitMut},
};

pub(crate) fn node_count<Metadata>(expression: &Expr<Metadata>) -> usize {
    struct Counter(usize);

    impl<Metadata> Visit<Metadata> for Counter {
        fn visit_expr(&mut self, expression: &Expr<Metadata>) {
            self.0 += 1;
            visit::visit_expr(self, expression);
        }
    }

    let mut counter = Counter(0);
    counter.visit_expr(expression);
    counter.0
}

pub(crate) fn contains_hole<Metadata>(expression: &Expr<Metadata>) -> bool {
    struct Finder(bool);

    impl<Metadata> Visit<Metadata> for Finder {
        fn visit_raw_expr_hole(&mut self) {
            self.0 = true;
        }
    }

    let mut finder = Finder(false);
    finder.visit_expr(expression);
    finder.0
}

/// Returns the unchanged expression and every distinct expression obtained by
/// replacing exactly one expression node, including the root, with a hole.
pub(crate) fn holeifications<Metadata>(expression: &Expr<Metadata>) -> Vec<Expr<Metadata>>
where
    Metadata: Clone + Default + Ord,
{
    let exact = deep_clone(expression);
    let mut generated = (0..node_count(expression))
        .map(|target| replace_node_with_hole(expression, target))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|candidate| candidate != &exact)
        .collect::<Vec<_>>();
    generated.sort_by(compare_holeifications);

    let mut result = vec![exact];
    result.extend(generated);
    result
}

/// Orders holeifications from most to least specific.
pub(crate) fn compare_holeifications<Metadata: Ord>(
    left: &Expr<Metadata>,
    right: &Expr<Metadata>,
) -> Ordering {
    contains_hole(left)
        .cmp(&contains_hole(right))
        .then_with(|| node_count(right).cmp(&node_count(left)))
        .then_with(|| left.cmp(right))
}

pub(crate) fn fill_holes<Metadata>(
    expression: &Expr<Metadata>,
    replacement: &Expr<Metadata>,
) -> Expr<Metadata>
where
    Metadata: Clone,
{
    struct Filler<'a, Metadata> {
        replacement: &'a Expr<Metadata>,
    }

    impl<Metadata: Clone> VisitMut<Metadata> for Filler<'_, Metadata> {
        fn visit_expr_mut(&mut self, context: VisitContext, expression: &mut Expr<Metadata>) {
            if matches!(expression.raw, RawExpr::Hole) {
                *expression = deep_clone(self.replacement);
            } else {
                visit_mut::visit_expr_mut(self, context, expression);
            }
        }

        fn visit_raw_expr_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<Metadata>,
        ) {
            visit_logic_chain_children(self, context, chain);
        }
    }

    let mut result = deep_clone(expression);
    Filler { replacement }.visit_expr_mut(VisitContext::positive(), &mut result);
    result
}

pub(crate) fn all_variables<'a, Metadata: 'a>(
    expressions: impl IntoIterator<Item = &'a Expr<Metadata>>,
) -> BTreeSet<Variable> {
    struct Collector(BTreeSet<Variable>);

    impl<Metadata> Visit<Metadata> for Collector {
        fn visit_variable(&mut self, variable: &Variable) {
            self.0.insert(variable.clone());
        }
    }

    let mut collector = Collector(BTreeSet::new());
    for expression in expressions {
        collector.visit_expr(expression);
    }
    collector.0
}

fn replace_node_with_hole<Metadata>(expression: &Expr<Metadata>, target: usize) -> Expr<Metadata>
where
    Metadata: Clone + Default,
{
    struct Holeifier {
        target: usize,
        current: usize,
        replaced: bool,
    }

    impl<Metadata: Default> VisitMut<Metadata> for Holeifier {
        fn visit_expr_mut(&mut self, context: VisitContext, expression: &mut Expr<Metadata>) {
            if self.replaced {
                return;
            }
            let current = self.current;
            self.current += 1;
            if current == self.target {
                *expression = Expr::new(RawExpr::Hole);
                self.replaced = true;
            } else {
                visit_mut::visit_expr_mut(self, context, expression);
            }
        }

        fn visit_raw_expr_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<Metadata>,
        ) {
            visit_logic_chain_children(self, context, chain);
        }
    }

    let mut result = deep_clone(expression);
    let mut holeifier = Holeifier {
        target,
        current: 0,
        replaced: false,
    };
    holeifier.visit_expr_mut(VisitContext::positive(), &mut result);
    assert!(holeifier.replaced, "holeification target must exist");
    result
}

fn visit_logic_chain_children<Metadata, Visitor>(
    visitor: &mut Visitor,
    context: VisitContext,
    chain: &mut LogicChain<Metadata>,
) where
    Visitor: VisitMut<Metadata> + ?Sized,
{
    visitor.visit_expr_mut(context.clone(), &mut chain.start);
    for (_, expression) in &mut chain.assertions {
        visitor.visit_expr_mut(context.clone(), expression);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{
        Binop, Cmp, Expr, Logic, LogicChain, Matrix, Range, RawExpr, SeqOp, TypeExpr, Variable,
    };

    use super::{all_variables, contains_hole, fill_holes, holeifications, node_count};

    fn natural(value: u64) -> Expr<()> {
        Expr::new(RawExpr::NatLiteral(value))
    }

    #[test]
    fn counts_and_holeifies_every_expression_node() {
        let cases = vec![
            (natural(1), 1),
            (
                Expr::new(RawExpr::Binop(Binop::Div, natural(1), natural(2))),
                3,
            ),
            (
                Expr::new(RawExpr::Matrix(Matrix {
                    rows: 1,
                    cols: 2,
                    elements: vec![natural(1), natural(2)],
                })),
                3,
            ),
            (
                Expr::new(RawExpr::Type(TypeExpr::Matrix(natural(1), natural(2)))),
                3,
            ),
            (
                Expr::new(RawExpr::Seqop(
                    SeqOp::Map,
                    Range {
                        index_variable: Variable::new("i"),
                        from: natural(1),
                        to: natural(2),
                    },
                    natural(3),
                )),
                4,
            ),
            (
                Expr::new(RawExpr::LogicChain(LogicChain {
                    start: natural(1),
                    assertions: vec![(Logic::Iff, natural(2)), (Logic::Imp, natural(3))],
                })),
                4,
            ),
        ];

        for (expression, expected_nodes) in cases {
            assert_eq!(node_count(&expression), expected_nodes);
            let variants = holeifications(&expression);
            assert_eq!(variants.len(), expected_nodes + 1);
            assert_eq!(variants[0], expression);
            assert!(variants[1..].iter().all(contains_hole));
            for mut variant in variants {
                assert!(variant.get_mut().is_some());
            }
        }
    }

    #[test]
    fn holeifications_preserve_retained_metadata_and_default_generated_holes() {
        let expression = Expr::with_metadata(
            9_u8,
            RawExpr::Binop(
                Binop::Div,
                Expr::with_metadata(8, RawExpr::NatLiteral(1)),
                Expr::with_metadata(7, RawExpr::NatLiteral(2)),
            ),
        );
        let variants = holeifications(&expression);
        let child_hole = variants
            .iter()
            .find(|variant| {
                matches!(
                    &variant.raw,
                    RawExpr::Binop(_, left, right)
                        if matches!(left.raw, RawExpr::Hole)
                            && matches!(right.raw, RawExpr::NatLiteral(2))
                )
            })
            .unwrap();
        let RawExpr::Binop(_, left, right) = &child_hole.raw else {
            unreachable!()
        };
        assert_eq!(child_hole.meta, 9);
        assert_eq!(left.meta, 0);
        assert_eq!(right.meta, 7);
        let root_hole = variants
            .iter()
            .find(|variant| matches!(variant.raw, RawExpr::Hole))
            .unwrap();
        assert_eq!(root_hole.meta, 0);
    }

    #[test]
    fn fills_holes_and_collects_bound_and_free_variable_names() {
        let expression = Expr::new(RawExpr::LogicChain(LogicChain {
            start: Expr::new(RawExpr::Hole),
            assertions: vec![(
                Logic::Imp,
                Expr::new(RawExpr::Seqop(
                    SeqOp::Sum,
                    Range {
                        index_variable: Variable::new("i"),
                        from: natural(1),
                        to: Expr::new(RawExpr::Variable(Variable::new("n"))),
                    },
                    Expr::new(RawExpr::Variable(Variable::new("i"))),
                )),
            )],
        }));
        let replacement = Expr::new(RawExpr::Variable(Variable::new("x")));
        let filled = fill_holes(&expression, &replacement);
        assert!(!contains_hole(&filled));
        assert_eq!(
            all_variables(std::iter::once(&filled)),
            ["i", "n", "x"]
                .map(Variable::new)
                .into_iter()
                .collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn larger_one_hole_variants_are_more_specific() {
        let expression = Expr::new(RawExpr::Binop(
            Binop::Div,
            Expr::new(RawExpr::Binop(Binop::Div, natural(1), natural(2))),
            natural(3),
        ));
        let variants = holeifications(&expression);
        let sizes = variants[1..].iter().map(node_count).collect::<Vec<_>>();
        assert!(sizes.windows(2).all(|pair| pair[0] >= pair[1]));
        assert!(matches!(variants.last().unwrap().raw, RawExpr::Hole));
    }

    #[test]
    fn identical_replacements_are_deduplicated() {
        let expression = Expr::new(RawExpr::CmpChain(crate::CmpChain {
            start: natural(1),
            assertions: vec![(Cmp::Eq, natural(1))],
        }));
        let variants = holeifications(&expression);
        assert_eq!(
            variants.iter().collect::<BTreeSet<_>>().len(),
            variants.len()
        );
    }
}
