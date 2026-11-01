use super::*;
use crate::{
    deep_clone::deep_clone,
    visit_mut::{self, VisitContext, VisitMut},
};

/// Alpha-rename only stored binders that would collide with a later declaration.
/// Binding metadata, rather than today's symbol table, decides what is bound.
pub(crate) fn avoid_bound_collisions(
    expression: &Expr<TypedMetadata>,
    occupied: &BTreeSet<Variable>,
) -> Expr<TypedMetadata> {
    struct Rename {
        used: BTreeSet<Variable>,
        names: BTreeMap<Variable, Variable>,
        next: usize,
    }
    impl Rename {
        fn ty(&mut self, ty: &TypeExpr<()>) -> TypeExpr<()> {
            let mut e = Expr::new(RawExpr::Type(ty.with_default_metadata::<TypedMetadata>()));
            self.visit_expr_mut(VisitContext::positive(), &mut e);
            let RawExpr::Type(t) = &e.raw else {
                unreachable!()
            };
            t.with_default_metadata()
        }
    }
    impl VisitMut<TypedMetadata> for Rename {
        fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
            if let Some(bindings) = node.meta.quantifier_bindings().cloned() {
                let previous = self.names.clone();
                for variable in bindings.introduced.keys() {
                    if self.used.contains(variable) {
                        let replacement = loop {
                            let candidate = Variable::new(format!("ndbound{}", self.next));
                            self.next += 1;
                            if self.used.insert(candidate.clone()) {
                                break candidate;
                            }
                        };
                        self.names.insert(variable.clone(), replacement);
                    } else {
                        self.names.remove(variable);
                        self.used.insert(variable.clone());
                    }
                }
                let renamed = bindings
                    .introduced
                    .iter()
                    .map(|(v, t)| {
                        (
                            self.names.get(v).cloned().unwrap_or_else(|| v.clone()),
                            self.ty(t),
                        )
                    })
                    .collect();
                visit_mut::visit_expr_mut(self, context, node);
                node.get_mut().unwrap().meta.quantifier = Some(QuantifierBindings {
                    introduced: renamed,
                });
                self.names = previous;
            } else {
                visit_mut::visit_expr_mut(self, context, node);
            }
        }
        fn visit_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<TypedMetadata>,
        ) {
            // Alpha-renaming is independent of logical polarity and applies to
            // surface biconditionals/chains before backend logic lowering.
            self.visit_expr_mut(context.clone(), &mut chain.start);
            for (_, expression) in &mut chain.assertions {
                self.visit_expr_mut(context.clone(), expression);
            }
        }
        fn visit_variable_mut(&mut self, _: VisitContext, v: &mut Variable) {
            if let Some(new) = self.names.get(v) {
                *v = new.clone();
            }
        }
    }
    let mut rename = Rename {
        used: occupied.clone(),
        names: BTreeMap::new(),
        next: 0,
    };
    let mut output = deep_clone(expression);
    rename.visit_expr_mut(VisitContext::positive(), &mut output);
    output
}
