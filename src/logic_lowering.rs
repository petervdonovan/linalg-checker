use crate::{
    Expr, Finop, Logic, LogicChain, MetaExpr, RawExpr,
    deep_clone::deep_clone,
    visit_mut::{self, VisitContext, VisitMut},
};

/// Rewrites adjacency-based logic chains into conjunctions of single
/// implications.
pub struct LogicLowering;

impl<Metadata: Clone> VisitMut<Metadata> for LogicLowering {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        let replacement = {
            let MetaExpr { meta, raw } = node
                .get_mut()
                .expect("logic lowering requires uniquely owned expressions");
            match raw {
                RawExpr::LogicChain(chain) if should_lower(chain) => Some(lower_chain(meta, chain)),
                _ => None,
            }
        };
        if let Some(replacement) = replacement {
            node.get_mut()
                .expect("logic lowering requires uniquely owned expressions")
                .raw = replacement;
        }
        visit_mut::visit_expr_mut(self, context, node);
    }
}

fn should_lower<Metadata>(chain: &LogicChain<Metadata>) -> bool {
    !matches!(chain.assertions.as_slice(), [] | [(Logic::Imp, _)])
}

fn lower_chain<Metadata: Clone>(
    metadata: &Metadata,
    chain: &LogicChain<Metadata>,
) -> RawExpr<Metadata> {
    let mut implications = Vec::new();
    let mut antecedent = &chain.start;
    for (op, consequent) in &chain.assertions {
        match op {
            Logic::Imp => {
                implications.push(implication(metadata, antecedent, consequent));
            }
            Logic::Iff => {
                implications.push(implication(metadata, antecedent, consequent));
                implications.push(implication(metadata, consequent, antecedent));
            }
        }
        antecedent = consequent;
    }
    RawExpr::Finop(Finop::And, implications)
}

fn implication<Metadata: Clone>(
    metadata: &Metadata,
    antecedent: &Expr<Metadata>,
    consequent: &Expr<Metadata>,
) -> Expr<Metadata> {
    Expr::with_metadata(
        metadata.clone(),
        RawExpr::LogicChain(LogicChain {
            start: deep_clone(antecedent),
            assertions: vec![(Logic::Imp, deep_clone(consequent))],
        }),
    )
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::LogicLowering;
    use crate::{
        Expr, Finop, Logic, RawExpr, from_tex,
        visit_mut::{VisitContext, VisitMut},
    };

    #[test]
    fn lowers_mixed_logic_chain_to_unique_single_implications() {
        let mut expression: Expr<()> =
            from_tex::expr(&parse(r"P \implies Q \iff R").expect("test input should be valid TeX"))
                .unwrap();
        let context = VisitContext {
            logical_polarity: true,
        };
        LogicLowering.visit_expr_mut(context, &mut expression);

        assert_eq!(
            expression.as_latex().to_string(),
            r"\left(P \implies Q\right) \land \left(Q \implies R\right) \land \left(R \implies Q\right)"
        );
        let RawExpr::Finop(Finop::And, implications) = &expression.raw else {
            panic!("expected a conjunction")
        };
        assert_eq!(implications.len(), 3);
        assert!(implications.iter().all(|implication| matches!(
            &implication.raw,
            RawExpr::LogicChain(chain)
                if matches!(chain.assertions.as_slice(), [(Logic::Imp, _)])
        )));

        struct Noop;
        impl VisitMut<()> for Noop {}
        Noop.visit_expr_mut(context, &mut expression);
    }
}
