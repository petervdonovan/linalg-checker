use std::collections::{BTreeSet, HashSet};

use crate::{
    Expr, Finop, LogicChain, RawExpr, Variable,
    deep_clone::deep_clone,
    visit::{self, Visit},
    visit_mut::{self, VisitContext, VisitMut},
};

const POSITIVE: VisitContext = VisitContext {
    logical_polarity: true,
    active_ranges: Vec::new(),
};

pub(crate) fn is_quantifier<Metadata>(expression: &Expr<Metadata>) -> bool {
    matches!(
        expression.raw,
        RawExpr::Finop(Finop::Forall | Finop::Exists, _)
    )
}

pub(crate) fn contains_quantifier<Metadata>(expression: &Expr<Metadata>) -> bool {
    #[derive(Default)]
    struct Finder(bool);

    impl<Metadata> Visit<Metadata> for Finder {
        fn visit_raw_expr_finop(&mut self, op: &Finop, expressions: &[Expr<Metadata>]) {
            if matches!(op, Finop::Forall | Finop::Exists) {
                self.0 = true;
            } else {
                visit::visit_raw_expr_finop(self, op, expressions);
            }
        }
    }

    let mut finder = Finder::default();
    finder.visit_expr(expression);
    finder.0
}

struct FreeVariableCollector {
    variables: BTreeSet<Variable>,
    bound: HashSet<Variable>,
}

impl<Metadata> Visit<Metadata> for FreeVariableCollector {
    fn visit_variable(&mut self, variable: &Variable) {
        if !self.bound.contains(variable) {
            self.variables.insert(variable.clone());
        }
    }

    fn visit_raw_expr_seqop(
        &mut self,
        _op: &crate::SeqOp,
        range: &crate::Range<Metadata>,
        body: &Expr<Metadata>,
    ) {
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
        assert!(
            self.bound.insert(range.index_variable.clone()),
            "sequence binder shadows an active binder"
        );
        self.visit_expr(body);
        self.bound.remove(&range.index_variable);
    }

    fn visit_raw_expr_finop(&mut self, op: &Finop, expressions: &[Expr<Metadata>]) {
        if !matches!(op, Finop::Forall | Finop::Exists) {
            visit::visit_raw_expr_finop(self, op, expressions);
            return;
        }
        let Some((body, premises)) = expressions.split_last() else {
            return;
        };
        let mut introduced = BTreeSet::new();
        for premise in premises {
            for variable in free_variables(std::iter::once(premise)) {
                if !self.variables.contains(&variable) && !self.bound.contains(&variable) {
                    introduced.insert(variable);
                }
            }
            self.bound.extend(introduced.iter().cloned());
            self.visit_expr(premise);
        }
        self.visit_expr(body);
        for variable in introduced {
            self.bound.remove(&variable);
        }
    }
}

pub(crate) fn free_variables<'a, Metadata: 'a>(
    expressions: impl Iterator<Item = &'a Expr<Metadata>>,
) -> BTreeSet<Variable> {
    let mut collector = FreeVariableCollector {
        variables: BTreeSet::new(),
        bound: HashSet::new(),
    };
    for expression in expressions {
        collector.visit_expr(expression);
    }
    collector.variables
}

pub(crate) fn quantifier_binders<Metadata>(
    expressions: &[Expr<Metadata>],
    accessible: &BTreeSet<Variable>,
) -> BTreeSet<Variable> {
    let Some((_, premises)) = expressions.split_last() else {
        return BTreeSet::new();
    };
    premises
        .iter()
        .flat_map(|premise| free_variables(std::iter::once(premise)))
        .filter(|variable| !accessible.contains(variable))
        .collect()
}

pub(crate) fn substitute_free_variable(
    expression: &Expr<()>,
    variable: &Variable,
    replacement: &Expr<()>,
) -> Expr<()> {
    struct Substitution<'a> {
        variable: &'a Variable,
        replacement: &'a Expr<()>,
    }

    impl VisitMut<()> for Substitution<'_> {
        fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<()>) {
            if matches!(&node.raw, RawExpr::Variable(variable) if variable == self.variable) {
                *node = deep_clone(self.replacement);
            } else {
                visit_mut::visit_expr_mut(self, context, node);
            }
        }

        fn visit_raw_expr_finop_mut(
            &mut self,
            context: VisitContext,
            op: &mut Finop,
            expressions: &mut Vec<Expr<()>>,
        ) {
            for expression in expressions.iter_mut() {
                self.visit_expr_mut(context.clone(), expression);
            }
            let mut flattened = Vec::new();
            for expression in expressions.drain(..) {
                if let RawExpr::Finop(nested_op, nested) = &expression.raw
                    && nested_op == op
                {
                    flattened.extend(nested.iter().map(deep_clone));
                } else {
                    flattened.push(expression);
                }
            }
            *expressions = flattened;
        }

        fn visit_raw_expr_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<()>,
        ) {
            self.visit_expr_mut(context.clone(), &mut chain.start);
            for (_, expression) in &mut chain.assertions {
                self.visit_expr_mut(context.clone(), expression);
            }
        }

        fn visit_raw_expr_seqop_mut(
            &mut self,
            context: VisitContext,
            _op: &mut crate::SeqOp,
            range: &mut crate::Range<()>,
            body: &mut Expr<()>,
        ) {
            self.visit_expr_mut(context.clone(), &mut range.from);
            self.visit_expr_mut(context.clone(), &mut range.to);
            if range.index_variable != *self.variable {
                self.visit_expr_mut(context.with_range(range), body);
            }
        }
    }

    let mut result = deep_clone(expression);
    Substitution {
        variable,
        replacement,
    }
    .visit_expr_mut(POSITIVE, &mut result);
    result
}
