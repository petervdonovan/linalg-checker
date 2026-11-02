use super::*;
use crate::{
    deep_clone::deep_clone,
    visit_mut::{self, VisitContext, VisitMut},
};

fn lexical_types(expression: &Expr<TypedMetadata>) -> SymbolicTypeEnvironment {
    use crate::visit::{self, Visit};
    struct Collect {
        types: SymbolicTypeEnvironment,
        bound: BTreeSet<Variable>,
    }
    impl Visit<TypedMetadata> for Collect {
        fn visit_expr(&mut self, e: &Expr<TypedMetadata>) {
            if let Some(bindings) = e.meta.quantifier_bindings() {
                let old = self.bound.clone();
                self.bound.extend(bindings.introduced.keys().cloned());
                visit::visit_expr(self, e);
                self.bound = old;
                return;
            }
            if let RawExpr::Variable(v) = &e.raw
                && !self.bound.contains(v)
                && let Ok(ty) = e.meta.get_type()
            {
                self.types.types.entry(v.clone()).or_insert(ty);
            }
            visit::visit_expr(self, e);
        }
        fn visit_raw_expr_seqop(
            &mut self,
            _: &SeqOp,
            range: &Range<TypedMetadata>,
            body: &Expr<TypedMetadata>,
        ) {
            self.visit_expr(&range.from);
            self.visit_expr(&range.to);
            let old = self.bound.clone();
            self.bound.insert(range.index_variable.clone());
            self.visit_expr(body);
            self.bound = old;
        }
        fn visit_raw_expr_set_comprehension(
            &mut self,
            v: &Variable,
            domain: &TypeExpr<TypedMetadata>,
            body: &Expr<TypedMetadata>,
        ) {
            self.visit_type_expr(domain);
            let old = self.bound.clone();
            self.bound.insert(v.clone());
            self.visit_expr(body);
            self.bound = old;
        }
    }
    let mut collector = Collect {
        types: SymbolicTypeEnvironment::default(),
        bound: BTreeSet::new(),
    };
    collector.visit_expr(expression);
    collector.types
}

/// Alpha-rename only stored binders that would collide with a later declaration.
/// Binding metadata, rather than today's symbol table, decides what is bound.
pub(crate) fn avoid_bound_collisions(
    expression: &Expr<TypedMetadata>,
    occupied: &BTreeSet<Variable>,
) -> Expr<TypedMetadata> {
    struct Conflicts<'a> {
        occupied: &'a BTreeSet<Variable>,
        found: bool,
    }
    impl crate::visit::Visit<TypedMetadata> for Conflicts<'_> {
        fn visit_raw_expr_seqop(
            &mut self,
            op: &SeqOp,
            range: &Range<TypedMetadata>,
            body: &Expr<TypedMetadata>,
        ) {
            self.found |= self.occupied.contains(&range.index_variable);
            crate::visit::visit_raw_expr_seqop(self, op, range, body);
        }
        fn visit_raw_expr_set_comprehension(
            &mut self,
            binder: &Variable,
            domain: &TypeExpr<TypedMetadata>,
            body: &Expr<TypedMetadata>,
        ) {
            self.found |= self.occupied.contains(binder);
            crate::visit::visit_raw_expr_set_comprehension(self, binder, domain, body);
        }
        fn visit_metadata(&mut self, meta: &TypedMetadata) {
            self.found |= meta
                .quantifier_bindings()
                .is_some_and(|b| b.introduced.keys().any(|v| self.occupied.contains(v)));
        }
    }
    let mut conflicts = Conflicts {
        occupied,
        found: false,
    };
    crate::visit::Visit::visit_expr(&mut conflicts, expression);
    if !conflicts.found {
        return expression.clone();
    }
    struct Rename {
        used: BTreeSet<Variable>,
        names: BTreeMap<Variable, Variable>,
        occupied: BTreeSet<Variable>,
    }
    impl Rename {
        fn enter(&mut self, original: &Variable) -> (Variable, Option<Variable>) {
            let replacement = if self.occupied.contains(original) {
                crate::expression_utils::fresh_variable_like(original, &mut self.used)
            } else {
                original.clone()
            };
            let previous = self.names.insert(original.clone(), replacement.clone());
            (replacement, previous)
        }
        fn leave(&mut self, original: Variable, previous: Option<Variable>) {
            self.names.remove(&original);
            if let Some(old) = previous {
                self.names.insert(original, old);
            }
        }
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
                    if self.occupied.contains(variable)
                        || self.names.values().any(|v| v == variable)
                    {
                        let replacement =
                            crate::expression_utils::fresh_variable_like(variable, &mut self.used);
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
        fn visit_metadata_mut(&mut self, _: VisitContext, meta: &mut TypedMetadata) {
            if let Some(ty) = meta.ty.take() {
                meta.ty = Some(self.ty(&ty));
            }
        }
        fn visit_raw_expr_seqop_mut(
            &mut self,
            context: VisitContext,
            _: &mut SeqOp,
            range: &mut Range<TypedMetadata>,
            body: &mut Expr<TypedMetadata>,
        ) {
            self.visit_expr_mut(context.clone(), &mut range.from);
            self.visit_expr_mut(context.clone(), &mut range.to);
            let original = range.index_variable.clone();
            let (renamed, previous) = self.enter(&original);
            range.index_variable = renamed;
            self.visit_expr_mut(context, body);
            self.leave(original, previous);
        }
        fn visit_raw_expr_set_comprehension_mut(
            &mut self,
            context: VisitContext,
            binder: &mut Variable,
            domain: &mut TypeExpr<TypedMetadata>,
            predicate: &mut Expr<TypedMetadata>,
        ) {
            self.visit_type_expr_mut(context.clone(), domain);
            let original = binder.clone();
            let (renamed, previous) = self.enter(&original);
            *binder = renamed;
            self.visit_expr_mut(context, predicate);
            self.leave(original, previous);
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
    let mut used = crate::expression_utils::all_typed_variables(expression);
    used.extend(occupied.iter().cloned());
    let mut rename = Rename {
        used,
        names: BTreeMap::new(),
        occupied: occupied.clone(),
    };
    let mut output = deep_clone(expression);
    rename.visit_expr_mut(VisitContext::positive(), &mut output);
    struct Clear;
    impl VisitMut<TypedMetadata> for Clear {
        fn visit_metadata_mut(&mut self, _: VisitContext, meta: &mut TypedMetadata) {
            meta.ty = None;
        }
        fn visit_logic_chain_mut(
            &mut self,
            context: VisitContext,
            chain: &mut LogicChain<TypedMetadata>,
        ) {
            self.visit_expr_mut(context.clone(), &mut chain.start);
            for (_, e) in &mut chain.assertions {
                self.visit_expr_mut(context.clone(), e);
            }
        }
    }
    Clear.visit_expr_mut(VisitContext::positive(), &mut output);
    TypeResolver::new_partial(&lexical_types(expression), &OperatorTypeRules::surface())
        .with_saved_bindings()
        .resolve(&mut output, VisitContext::positive())
        .expect("capture-safe renaming preserves typing");
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    fn var(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }
    fn nat(n: u64) -> Expr<()> {
        Expr::new(RawExpr::NatLiteral(n))
    }
    fn eq(a: Expr<()>, b: Expr<()>) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(crate::CmpChain {
            start: a,
            assertions: vec![(crate::Cmp::Eq, b)],
        }))
    }
    fn quantified(name: &str, ty: TypeExpr<()>, body: Expr<()>) -> Expr<()> {
        Expr::new(RawExpr::Finop(
            Finop::Forall,
            vec![
                Expr::new(RawExpr::Binop(
                    Binop::ElementOf,
                    var(name),
                    Expr::new(RawExpr::Type(ty)),
                )),
                body,
            ],
        ))
    }

    #[test]
    fn sequence_shadowing_keeps_endpoints_in_the_outer_scope() {
        let sum = |index: &str| {
            Expr::new(RawExpr::Seqop(
                SeqOp::Sum,
                Range {
                    index_variable: Variable::new(index),
                    from: nat(1),
                    to: var("n"),
                },
                var(index),
            ))
        };
        let source = quantified("n", TypeExpr::Nat, eq(sum("n"), sum("j")));
        let typed = analyze_formula(&SymbolicTypeEnvironment::default(), &source).unwrap();
        let renamed = avoid_bound_collisions(&typed, &BTreeSet::from([Variable::new("n")]));
        let binder = renamed
            .meta
            .quantifier_bindings()
            .unwrap()
            .introduced
            .keys()
            .next()
            .unwrap();
        assert_ne!(binder, &Variable::new("n"));
        let RawExpr::Finop(_, parts) = &renamed.raw else {
            panic!()
        };
        let RawExpr::CmpChain(body) = &parts[1].raw else {
            panic!()
        };
        let RawExpr::Seqop(_, range, term) = &body.start.raw else {
            panic!()
        };
        assert_ne!(&range.index_variable, binder);
        assert!(matches!(&range.to.raw,RawExpr::Variable(v) if v==binder));
        assert!(matches!(&term.raw,RawExpr::Variable(v) if *v==range.index_variable));
    }

    #[test]
    fn set_domains_use_outer_binders_and_predicates_use_their_own_binder() {
        let set = Expr::new(RawExpr::SetComprehension {
            variable: Variable::new("n"),
            domain: TypeExpr::Matrix(var("n"), nat(1)),
            predicate: eq(var("n"), var("n")),
        });
        let source = quantified(
            "n",
            TypeExpr::Nat,
            eq(crate::deep_clone::deep_clone(&set), set),
        );
        let typed = analyze_formula(&SymbolicTypeEnvironment::default(), &source).unwrap();
        let renamed = avoid_bound_collisions(&typed, &BTreeSet::from([Variable::new("n")]));
        let binder = renamed
            .meta
            .quantifier_bindings()
            .unwrap()
            .introduced
            .keys()
            .next()
            .unwrap();
        let RawExpr::Finop(_, parts) = &renamed.raw else {
            panic!()
        };
        let RawExpr::CmpChain(body) = &parts[1].raw else {
            panic!()
        };
        let RawExpr::SetComprehension {
            variable,
            domain,
            predicate,
        } = &body.start.raw
        else {
            panic!()
        };
        assert_ne!(variable, binder);
        let TypeExpr::Matrix(rows, _) = domain else {
            panic!()
        };
        assert!(matches!(&rows.raw,RawExpr::Variable(v) if v==binder));
        let RawExpr::CmpChain(predicate) = &predicate.raw else {
            panic!()
        };
        assert!(matches!(&predicate.start.raw,RawExpr::Variable(v) if v==variable));
        assert!(
            matches!(predicate.start.meta.get_type().unwrap(),TypeExpr::Matrix(ref rows,_) if matches!(&rows.raw,RawExpr::Variable(v) if v==binder))
        );
    }

    #[test]
    fn generated_names_avoid_names_present_only_in_type_annotations() {
        let mut prime = Variable::new("x");
        prime.annotations.push(crate::Annotation::Prime);
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(
                Variable::new("A"),
                TypeExpr::Matrix(Expr::new(RawExpr::Variable(prime.clone())), nat(1)),
            )]),
        };
        let source = quantified("x", TypeExpr::Real, eq(var("A"), var("A")));
        let typed = analyze_formula(&types, &source).unwrap();
        let renamed = avoid_bound_collisions(&typed, &BTreeSet::from([Variable::new("x")]));
        assert!(
            !renamed
                .meta
                .quantifier_bindings()
                .unwrap()
                .introduced
                .contains_key(&prime)
        );
    }
}

#[cfg(test)]
mod later_sequence_declaration_test {
    use super::*;
    #[test]
    fn a_later_free_index_name_does_not_invalidate_a_stored_sum() {
        let expression =
            crate::from_tex::expr(&ratex_parser::parse(r"\sum_{i=1}^{2}i = 3").unwrap()).unwrap();
        let original = analyze_formula(&SymbolicTypeEnvironment::default(), &expression).unwrap();
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(Variable::new("i"), TypeExpr::Nat)]),
        };
        let normalized = avoid_bound_collisions(&original, &types.types.keys().cloned().collect());
        crate::preprocessing::prepare_expression(
            &types,
            &normalized.with_default_metadata::<()>(),
            VisitContext::positive(),
        )
        .unwrap();
    }
}
