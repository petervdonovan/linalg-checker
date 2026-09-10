use std::collections::HashMap;

use crate::{
    Binop, Expr, Logic, Monop, RawExpr,
    logic_lowering::LogicLowering,
    operator_visitors::{Norm2SquaredVisitor, Norm2Visitor, SquareRootVisitor, assert_compatible},
    type_resolver::{
        MaybeTyped, OperatorTypeRules, TypeError, TypeLookup, TypeResolver, TypedMetadata,
    },
    visit::{self, Visit},
    visit_mut::{Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Clone, Debug)]
pub struct PreparedExpression {
    pub expression: Expr<TypedMetadata>,
    pub side_conditions: Vec<SideCondition<TypedMetadata>>,
    pub context: VisitContext,
}

impl PreparedExpression {
    /// Compose an exported implication without erasing annotations or losing
    /// definitions introduced while interpreting its givens and conclusion.
    pub(crate) fn under_givens(mut self, givens: &[Self]) -> Self {
        if givens.is_empty() {
            return self;
        }
        let bool_meta = TypedMetadata::resolved(crate::TypeExpr::Bool);
        let antecedent = if let [given] = givens {
            given.expression.clone()
        } else {
            Expr::with_metadata(
                bool_meta.clone(),
                RawExpr::Finop(
                    crate::Finop::And,
                    givens
                        .iter()
                        .map(|given| given.expression.clone())
                        .collect(),
                ),
            )
        };
        self.expression = Expr::with_metadata(
            bool_meta,
            RawExpr::LogicChain(crate::LogicChain {
                start: antecedent,
                assertions: vec![(Logic::Imp, self.expression)],
            }),
        );
        for given in givens {
            merge_side_conditions(&mut self.side_conditions, given.side_conditions.clone());
        }
        self
    }
}

pub fn prepare_expression<Metadata, Lookup: TypeLookup>(
    types: &Lookup,
    expression: &Expr<Metadata>,
    context: VisitContext,
) -> Result<PreparedExpression, TypeError> {
    prepare_expression_inner(types, expression, context, None)
}

/// Prepare using fully prepared, ellipsis-free givens as interpretation premises.
pub fn prepare_expression_with_premises<Metadata>(
    types: &crate::type_resolver::SymbolicTypeEnvironment,
    expression: &Expr<Metadata>,
    context: VisitContext,
    premises: &[PreparedExpression],
    max_dimension: u64,
) -> Result<PreparedExpression, TypeError> {
    prepare_expression_inner(
        types,
        expression,
        context,
        Some((types, premises, max_dimension)),
    )
}

/// Givens are interpreted in order; a given never supplies its own evidence.
pub fn prepare_givens(
    types: &crate::type_resolver::SymbolicTypeEnvironment,
    givens: &[Expr<()>],
    enclosing: &[PreparedExpression],
    max_dimension: u64,
) -> Result<Vec<PreparedExpression>, TypeError> {
    let mut scope = enclosing.to_vec();
    for given in givens {
        let prepared = prepare_expression_with_premises(
            types,
            given,
            VisitContext::positive(),
            &scope,
            max_dimension,
        )?;
        scope.push(prepared);
    }
    Ok(scope.split_off(enclosing.len()))
}

fn prepare_expression_inner<Metadata, Lookup: TypeLookup>(
    types: &Lookup,
    expression: &Expr<Metadata>,
    context: VisitContext,
    synthesis: Option<(
        &crate::type_resolver::SymbolicTypeEnvironment,
        &[PreparedExpression],
        u64,
    )>,
) -> Result<PreparedExpression, TypeError> {
    let mut expression: Expr<TypedMetadata> = expression.with_default_metadata();
    let core_rules = OperatorTypeRules::core();
    let mut side_conditions = Vec::new();

    // Typing is monotone: rewrites preserve valid annotations, while new nodes
    // start untyped and are completed on a later pass over the whole forest.
    loop {
        let synthetic_types = side_conditions
            .iter()
            .map(|condition: &SideCondition<TypedMetadata>| {
                (
                    condition.introduced_variable.clone(),
                    condition.introduced_type.clone(),
                )
            })
            .collect();
        let extended_types = ExtendedTypeLookup {
            base: types,
            synthetic_types,
        };
        resolve_forest(
            &extended_types,
            &core_rules,
            context.clone(),
            &mut expression,
            &mut side_conditions,
        )?;

        let mut rewrites = 0;
        let mut logic = LogicLowering::default();
        visit_forest(
            &mut logic,
            context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += logic.rewrites();

        let mut norm2_squared = Norm2SquaredVisitor::default();
        visit_forest(
            &mut norm2_squared,
            context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += norm2_squared.finish()?;

        let mut norm2 = Norm2Visitor::default();
        visit_forest(
            &mut norm2,
            context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        let (norm_rewrites, conditions) = norm2.finish()?;
        rewrites += norm_rewrites;
        merge_side_conditions(&mut side_conditions, conditions);

        let mut square_roots = SquareRootVisitor::default();
        visit_forest(
            &mut square_roots,
            context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        let (root_rewrites, conditions) = square_roots.finish()?;
        rewrites += root_rewrites;
        merge_side_conditions(&mut side_conditions, conditions);

        if let Some((types, premises, max_dimension)) = synthesis {
            let mut synthesis_types = types.clone();
            for condition in premises
                .iter()
                .flat_map(|premise| &premise.side_conditions)
                .chain(&side_conditions)
            {
                synthesis_types.types.insert(
                    condition.introduced_variable.clone(),
                    condition.introduced_type.clone(),
                );
            }
            let mut ellipses = crate::ellipsis_elimination::EllipsisElimination::new(
                &synthesis_types,
                premises,
                max_dimension,
            );
            visit_forest(
                &mut ellipses,
                context.clone(),
                &mut expression,
                &mut side_conditions,
            );
            rewrites += ellipses
                .finish()
                .map_err(|error| TypeError::Ellipsis(Box::new(error)))?;
        }

        if rewrites == 0 {
            validate_forest(&core_rules, &expression, &side_conditions)?;
            break;
        }
    }

    Ok(PreparedExpression {
        expression,
        side_conditions,
        context,
    })
}

fn visit_forest<V: VisitMut<TypedMetadata>>(
    visitor: &mut V,
    context: VisitContext,
    expression: &mut Expr<TypedMetadata>,
    side_conditions: &mut [SideCondition<TypedMetadata>],
) {
    visitor.visit_expr_mut(context.clone(), expression);
    for condition in side_conditions {
        let condition_context = context.with_active_ranges(&condition.active_ranges);
        for assertion in &mut condition.defining_assertions {
            visitor.visit_expr_mut(condition_context.clone(), assertion);
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                visitor.visit_expr_mut(condition_context.clone(), assertion);
            }
        }
    }
}

fn resolve_forest<Lookup: TypeLookup>(
    types: &Lookup,
    rules: &OperatorTypeRules,
    context: VisitContext,
    expression: &mut Expr<TypedMetadata>,
    side_conditions: &mut [SideCondition<TypedMetadata>],
) -> Result<(), TypeError> {
    TypeResolver::new(types, rules).resolve(expression, context.clone())?;
    for condition in side_conditions {
        let condition_context = context.with_active_ranges(&condition.active_ranges);
        for assertion in &mut condition.defining_assertions {
            TypeResolver::new(types, rules).resolve(assertion, condition_context.clone())?;
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                TypeResolver::new(types, rules).resolve(assertion, condition_context.clone())?;
            }
        }
    }
    Ok(())
}

fn merge_side_conditions(
    existing: &mut Vec<SideCondition<TypedMetadata>>,
    new: Vec<SideCondition<TypedMetadata>>,
) {
    for condition in new {
        if let Some(previous) = existing
            .iter()
            .find(|previous| previous.introduced_variable == condition.introduced_variable)
        {
            assert_compatible(previous, &condition);
        } else {
            existing.push(condition);
        }
    }
}

fn validate_forest(
    rules: &OperatorTypeRules,
    expression: &Expr<TypedMetadata>,
    side_conditions: &[SideCondition<TypedMetadata>],
) -> Result<(), TypeError> {
    let mut validator = CompletenessValidator { rules, error: None };
    validator.visit_expr(expression);
    for condition in side_conditions {
        for assertion in &condition.defining_assertions {
            validator.visit_expr(assertion);
        }
        if let Existence::Checkable(assertions) = &condition.existence {
            for assertion in assertions {
                validator.visit_expr(assertion);
            }
        }
    }
    validator.error.map_or(Ok(()), Err)
}

struct CompletenessValidator<'a> {
    rules: &'a OperatorTypeRules,
    error: Option<TypeError>,
}

impl Visit<TypedMetadata> for CompletenessValidator<'_> {
    fn visit_expr(&mut self, node: &Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        self.error = match &node.raw {
            RawExpr::Monop(Monop::Norm2, _) => {
                Some(TypeError::Unsupported("2-norm remains after preprocessing"))
            }
            RawExpr::Binop(Binop::Power, _, exponent) if is_half(exponent) => Some(
                TypeError::Unsupported("square root remains after preprocessing"),
            ),
            RawExpr::LogicChain(chain)
                if !matches!(chain.assertions.as_slice(), [] | [(Logic::Imp, _)]) =>
            {
                Some(TypeError::Unsupported(
                    "logic chain remains after preprocessing",
                ))
            }
            _ => None,
        };
        if self.error.is_some() {
            return;
        }
        visit::visit_expr(self, node);
        if self.error.is_some() {
            return;
        }
        self.error = match &node.raw {
            RawExpr::Monop(op, _) if !self.rules.supports_monop(*op) => {
                Some(TypeError::Unsupported("unregistered unary operator"))
            }
            RawExpr::Binop(op, _, _) if !self.rules.supports_binop(*op) => {
                Some(TypeError::Unsupported("unregistered binary operator"))
            }
            RawExpr::Triop(op, _, _, _) if !self.rules.supports_triop(*op) => {
                Some(TypeError::Unsupported("unregistered ternary operator"))
            }
            RawExpr::Finop(op, _) if !self.rules.supports_finop(*op) => {
                Some(TypeError::Unsupported("unregistered finite operator"))
            }
            RawExpr::Seqop(op, _, _) if !self.rules.supports_seqop(*op) => {
                Some(TypeError::Unsupported("unregistered sequence operator"))
            }
            RawExpr::Hole | RawExpr::Type(_) => None,
            RawExpr::Ellipsis => Some(TypeError::Unsupported(
                "ellipses must be eliminated before preprocessing completes",
            )),
            _ if node.meta.get_type().is_err() => Some(TypeError::Unsupported(
                "expression remains untyped after preprocessing",
            )),
            _ => None,
        };
    }

    fn visit_raw_expr_binop(
        &mut self,
        op: &Binop,
        left: &Expr<TypedMetadata>,
        right: &Expr<TypedMetadata>,
    ) {
        if matches!(op, Binop::ElementOf) && matches!(left.raw, RawExpr::Variable(_)) {
            self.visit_expr(right);
        } else if matches!(op, Binop::Cast) {
            if matches!(left.raw, RawExpr::Type(_)) {
                self.visit_expr(left);
            }
            self.visit_expr(right);
        } else {
            visit::visit_raw_expr_binop(self, op, left, right);
        }
    }
}

fn is_half<Metadata>(expression: &Expr<Metadata>) -> bool {
    matches!(
        &expression.raw,
        RawExpr::Binop(Binop::Div, numerator, denominator)
            if matches!(numerator.raw, RawExpr::NatLiteral(1))
                && matches!(denominator.raw, RawExpr::NatLiteral(2))
    )
}

struct ExtendedTypeLookup<'a, Lookup> {
    base: &'a Lookup,
    synthetic_types: HashMap<crate::Variable, crate::TypeExpr<()>>,
}

impl<Lookup: TypeLookup> TypeLookup for ExtendedTypeLookup<'_, Lookup> {
    fn type_of(&self, variable: &crate::Variable) -> Option<crate::TypeExpr<()>> {
        self.synthetic_types
            .get(variable)
            .cloned()
            .or_else(|| self.base.type_of(variable))
    }
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::prepare_expression;
    use crate::{
        Binop, Cmp, Expr, Finop, RawExpr, TypeExpr,
        enumerable_envspec::infer_symbolic_type_environment,
        from_tex,
        type_resolver::{MaybeTyped, SymbolicTypeEnvironment},
        visit_mut::{Existence, VisitContext},
    };

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
        active_ranges: Vec::new(),
    };

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
    }

    fn prepare(tex: &str, assumptions: &[&str]) -> Result<super::PreparedExpression, String> {
        let assumptions = assumptions
            .iter()
            .map(|tex| expression(tex))
            .collect::<Vec<_>>();
        let types = infer_symbolic_type_environment(&assumptions).unwrap();
        prepare_expression(&types, &expression(tex), POSITIVE).map_err(|error| error.to_string())
    }

    #[test]
    fn implicit_constant_roots_have_distinct_internal_names_and_common_display_names() {
        let parsed: Expr<()> =
            from_tex::expr(&parse(r"\mathbb{0}^{\frac{1}{2}} + \mathbb{0}^{\frac{1}{2}}").unwrap())
                .unwrap();
        let prepared =
            prepare_expression(&SymbolicTypeEnvironment::default(), &parsed, POSITIVE).unwrap();
        assert_eq!(prepared.side_conditions.len(), 2);
        assert_ne!(
            prepared.side_conditions[0].introduced_variable,
            prepared.side_conditions[1].introduced_variable
        );
        assert_eq!(
            prepared.side_conditions[0].display_name,
            prepared.side_conditions[1].display_name
        );
        assert!(!prepared.side_conditions[0].display_name.contains("dim"));
    }

    #[test]
    fn squared_two_norm_lowers_directly_to_a_scalar_gram_product() {
        let prepared = prepare(
            r"\left\lVert v \right\rVert_{2}^{2}",
            &[r"v \in \mathbb{R}^{d}"],
        )
        .unwrap();

        assert_eq!(
            prepared.expression.as_latex().to_string(),
            r"\operatorname{cast}(\mathbb{R}, v^\top v)"
        );
        assert!(prepared.side_conditions.is_empty());
        assert_eq!(prepared.expression.meta.get_type().unwrap(), TypeExpr::Real);
    }

    #[test]
    fn two_norm_introduces_a_guaranteed_nonnegative_principal_root() {
        let prepared = prepare(
            r"\left\lVert v \right\rVert_{2}",
            &[r"v \in \mathbb{R}^{d}"],
        )
        .unwrap();

        let RawExpr::Variable(introduced) = &prepared.expression.raw else {
            panic!("2-norm was not replaced by a synthetic variable")
        };
        assert_eq!(introduced.name, r"\left\lVert v \right\rVert_{2}");
        let [condition] = prepared.side_conditions.as_slice() else {
            panic!("expected one norm side condition")
        };
        assert_eq!(condition.introduced_variable, *introduced);
        assert_eq!(condition.introduced_type, TypeExpr::Real);
        assert!(matches!(condition.existence, Existence::Guaranteed));
        assert_eq!(condition.defining_assertions.len(), 2);

        let RawExpr::CmpChain(square) = &condition.defining_assertions[0].raw else {
            panic!("first definition must be an equality")
        };
        assert_eq!(square.assertions[0].0, Cmp::Eq);
        assert!(matches!(square.start.raw, RawExpr::Finop(Finop::Times, _)));
        assert_eq!(
            square.assertions[0].1.as_latex().to_string(),
            r"\operatorname{cast}(\mathbb{R}, v^\top v)"
        );
        let RawExpr::CmpChain(nonnegative) = &condition.defining_assertions[1].raw else {
            panic!("second definition must be a comparison")
        };
        assert_eq!(nonnegative.assertions[0].0, Cmp::Ge);
    }

    #[test]
    fn repeated_norms_deduplicate_but_distinct_implicit_operands_do_not() {
        let repeated = prepare(
            r"\left\lVert v \right\rVert_{2} + \left\lVert v \right\rVert_{2}",
            &[r"v \in \mathbb{R}^{d}"],
        )
        .unwrap();
        assert_eq!(repeated.side_conditions.len(), 1);

        let distinct = prepare_expression(
            &SymbolicTypeEnvironment::default(),
            &expression(
                r"\left\lVert \mathbb{0} \right\rVert_{2} + \left\lVert \mathbb{0} \right\rVert_{2}",
            ),
            POSITIVE,
        )
        .unwrap();
        assert_eq!(distinct.side_conditions.len(), 2);
        assert_ne!(
            distinct.side_conditions[0].introduced_variable,
            distinct.side_conditions[1].introduced_variable
        );
        assert_eq!(
            distinct.side_conditions[0].display_name,
            distinct.side_conditions[1].display_name
        );
    }

    #[test]
    fn two_norm_rejects_nonmatrix_operands() {
        let error = prepare(r"\left\lVert a \right\rVert_{2}", &[r"a \in \mathbb{R}"]).unwrap_err();
        assert_eq!(error, "2-norm requires a real column matrix");
    }

    #[test]
    fn later_visitors_process_generated_conditions_and_deduplicate_across_trees() {
        let prepared = prepare(
            r"\left\lVert A^{\frac{1}{2}} \right\rVert_{2} = 0 \land A^{\frac{1}{2}} = A^{\frac{1}{2}}",
            &[r"A \in \mathbb{R}^{d \times d}"],
        )
        .unwrap();

        assert_eq!(prepared.side_conditions.len(), 2);
        assert!(matches!(
            prepared.side_conditions[0].existence,
            Existence::Guaranteed
        ));
        assert!(matches!(
            prepared.side_conditions[1].existence,
            Existence::Assumed
        ));
    }

    #[test]
    fn typing_and_lowering_reach_a_fixpoint_across_the_whole_forest() {
        let prepared = prepare(
            r"\left(\left\lVert v \right\rVert_{2} + 1\right)^{\frac{1}{2}}",
            &[r"v \in \mathbb{R}^{d}"],
        )
        .unwrap();

        assert!(matches!(prepared.expression.raw, RawExpr::Variable(_)));
        assert_eq!(prepared.expression.meta.get_type().unwrap(), TypeExpr::Real);
        assert_eq!(prepared.side_conditions.len(), 2);
        assert!(
            prepared
                .side_conditions
                .iter()
                .any(|condition| matches!(condition.existence, Existence::Guaranteed))
        );
        assert!(
            prepared
                .side_conditions
                .iter()
                .any(|condition| matches!(condition.existence, Existence::Checkable(_)))
        );
        assert!(prepared.side_conditions.iter().all(|condition| {
            condition
                .defining_assertions
                .iter()
                .all(|assertion| assertion.meta.get_type() == Ok(TypeExpr::Bool))
        }));
    }

    #[test]
    fn roots_under_sequence_operations_are_lifted_pointwise() {
        let prepared = prepare(
            r"\sum_{i=1}^{n}\lambda_i^{\frac{1}{2}}",
            &[r"\lambda \in \operatorname{Seq}_{n}(\mathbb{R})"],
        )
        .unwrap();

        let [condition] = prepared.side_conditions.as_slice() else {
            panic!("expected one lifted root condition")
        };
        assert_eq!(condition.active_ranges.len(), 1);
        assert!(matches!(condition.introduced_type, TypeExpr::Seq(_, _)));
        assert!(
            condition
                .introduced_variable
                .name
                .contains("operatorname{map}")
        );
        let RawExpr::Seqop(crate::SeqOp::Sum, _, body) = &prepared.expression.raw else {
            panic!("expected the original sum")
        };
        assert!(matches!(
            body.raw,
            RawExpr::Binop(Binop::SingleSubscript, _, _)
        ));
    }

    #[test]
    fn generated_values_under_nested_ranges_use_nested_sequences() {
        let prepared = prepare(
            r"\sum_{i=1}^{2}\sum_{j=1}^{3}\left(x + i + j\right)^{\frac{1}{2}}",
            &[r"x \in \mathbb{R}"],
        )
        .unwrap();
        let [condition] = prepared.side_conditions.as_slice() else {
            panic!("expected one nested pointwise condition")
        };
        assert_eq!(condition.active_ranges.len(), 2);
        let TypeExpr::Seq(outer, _) = &condition.introduced_type else {
            panic!("expected an outer sequence")
        };
        assert!(matches!(outer.raw, RawExpr::Type(TypeExpr::Seq(_, _))));
    }

    #[test]
    fn completion_rejects_a_surface_operator_that_cannot_make_progress() {
        let half: Expr<()> = Expr::new(RawExpr::Binop(
            Binop::Div,
            Expr::new(RawExpr::NatLiteral(1)),
            Expr::new(RawExpr::NatLiteral(2)),
        ));
        let root = Expr::new(RawExpr::Binop(Binop::Power, Expr::new(RawExpr::Hole), half));
        let root = root.with_default_metadata();
        assert_eq!(
            super::validate_forest(&crate::type_resolver::OperatorTypeRules::core(), &root, &[],)
                .unwrap_err(),
            crate::type_resolver::TypeError::Unsupported("square root remains after preprocessing")
        );
    }
    fn prepare_with_givens(
        tex: &str,
        givens: &[&str],
    ) -> Result<super::PreparedExpression, crate::type_resolver::TypeError> {
        let givens = givens.iter().map(|tex| expression(tex)).collect::<Vec<_>>();
        let types = infer_symbolic_type_environment(&givens).unwrap();
        let premises = super::prepare_givens(&types, &givens, &[], 3)?;
        super::prepare_expression_with_premises(&types, &expression(tex), POSITIVE, &premises, 3)
    }

    #[test]
    fn eliminates_multiple_nested_literals_and_finishes_typing() {
        let prepared = prepare_with_givens(
            r"\operatorname{diag}(c_1, \ldots, c_n) = \operatorname{diag}(c_1, \ldots, c_n)",
            &[
                r"n \in \mathbb{N}",
                r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            ],
        )
        .unwrap();
        assert_eq!(prepared.expression.meta.get_type(), Ok(TypeExpr::Bool));
        assert!(!prepared.expression.as_latex().to_string().contains("ldots"));
    }

    #[test]
    fn synthesis_enables_root_lowering_in_the_same_fixpoint() {
        let prepared = prepare_with_givens(
            r"\left(\operatorname{diag}(c_1, \ldots, c_n)\right)^{\frac{1}{2}}",
            &[
                r"n \in \mathbb{N}",
                r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            ],
        )
        .unwrap();
        assert!(matches!(prepared.expression.raw, RawExpr::Variable(_)));
        assert_eq!(prepared.side_conditions.len(), 1);
        assert!(
            !prepared.side_conditions[0].defining_assertions[0]
                .as_latex()
                .to_string()
                .contains("ldots")
        );
    }

    #[test]
    fn synthesis_preserves_root_anchor_patterns_and_lifts_definitions() {
        let prepared = prepare_with_givens(
            r"\operatorname{diag}(c_1^{\frac{1}{2}}, \ldots, c_n^{\frac{1}{2}})",
            &[
                r"n \in \mathbb{N}",
                r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            ],
        )
        .unwrap();
        assert_eq!(prepared.side_conditions.len(), 1);
        assert_eq!(prepared.side_conditions[0].active_ranges.len(), 1);
    }

    #[test]
    fn synthesis_checks_every_lexical_index_without_exporting_it() {
        let prepared = prepare_with_givens(
            r"\sum_{j=1}^{n}\det(\operatorname{diag}(c_1 + j, \ldots, c_n + j))",
            &[
                r"n \in \mathbb{N}",
                r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            ],
        )
        .unwrap();
        assert!(!prepared.expression.as_latex().to_string().contains("ldots"));
        assert!(prepared.context.active_ranges.is_empty());
    }

    #[test]
    fn target_equality_cannot_justify_its_own_anchors() {
        let result = prepare_with_givens(
            r"\operatorname{diag}(c_1, \ldots, d_n) = \operatorname{diag}(c)",
            &[
                r"n \in \mathbb{N}",
                r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
                r"d \in \operatorname{Seq}_{n}(\mathbb{R})",
            ],
        );
        assert!(matches!(
            result,
            Err(crate::type_resolver::TypeError::Ellipsis(_))
        ));
    }

    #[test]
    fn ellipsis_in_generated_norm_definitions_is_eliminated() {
        let prepared = prepare_with_givens(
            r"\left\lVert \operatorname{diag}(c_1, \ldots, c_n)e_1 \right\rVert_{2}",
            &[r"n = 2", r"c \in \operatorname{Seq}_{n}(\mathbb{R})"],
        )
        .unwrap();
        assert_eq!(prepared.side_conditions.len(), 1);
        for condition in &prepared.side_conditions {
            for assertion in &condition.defining_assertions {
                assert!(!crate::ellipsis_elimination::contains_ellipses(assertion));
                assert_eq!(assertion.meta.get_type(), Ok(TypeExpr::Bool));
            }
        }
    }

    #[test]
    fn given_interpretation_uses_preceding_but_not_later_givens() {
        let declarations = [
            r"n = 2",
            r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            r"d \in \operatorname{Seq}_{n}(\mathbb{R})",
        ];
        let mixed = r"A = \operatorname{diag}(c_1, \ldots, d_n)";
        let evidence = r"\operatorname{diag}(c) = \operatorname{diag}(d)";
        let before = declarations
            .into_iter()
            .chain([mixed, evidence])
            .collect::<Vec<_>>();
        assert!(prepare_with_givens("0 = 0", &before).is_err());
        let after = declarations
            .into_iter()
            .chain([evidence, mixed])
            .collect::<Vec<_>>();
        assert!(prepare_with_givens("0 = 0", &after).is_ok());
    }

    #[test]
    fn nested_ellipsis_anchors_are_interpreted_inside_out() {
        let givens = [
            expression(r"n = 2"),
            expression(r"c \in \operatorname{Seq}_{n}(\mathbb{R})"),
        ];
        let types = infer_symbolic_type_environment(&givens).unwrap();
        let premises = super::prepare_givens(&types, &givens, &[], 2).unwrap();
        let inner = expression(r"c_1, \ldots, c_n");
        let outer = Expr::new(RawExpr::Finop(
            Finop::SeqLiteral,
            vec![inner.clone(), Expr::new(RawExpr::Ellipsis), inner],
        ));
        let prepared =
            super::prepare_expression_with_premises(&types, &outer, POSITIVE, &premises, 2)
                .unwrap();
        assert!(!crate::ellipsis_elimination::contains_ellipses(
            &prepared.expression
        ));
        let TypeExpr::Seq(element, _) = prepared.expression.meta.get_type().unwrap() else {
            panic!("expected sequence")
        };
        assert!(matches!(element.raw, RawExpr::Type(TypeExpr::Seq(_, _))));
    }

    #[test]
    fn synthesis_visits_checkable_existence_assertions() {
        let givens = [
            expression(r"n = 2"),
            expression(r"c \in \operatorname{Seq}_{n}(\mathbb{R})"),
        ];
        let types = infer_symbolic_type_environment(&givens).unwrap();
        let premises = super::prepare_givens(&types, &givens, &[], 2).unwrap();
        let mut main = expression("0 = 0").with_default_metadata();
        let mut conditions = vec![crate::visit_mut::SideCondition {
            introduced_variable: crate::Variable::new("root"),
            display_name: "root".into(),
            introduced_type: TypeExpr::Real,
            active_ranges: Vec::new(),
            defining_assertions: Vec::new(),
            existence: Existence::Checkable(vec![
                expression(r"\operatorname{diag}(c_1, \ldots, c_n) = \operatorname{diag}(c)")
                    .with_default_metadata(),
            ]),
        }];
        let rules = crate::type_resolver::OperatorTypeRules::core();
        super::resolve_forest(&types, &rules, POSITIVE, &mut main, &mut conditions).unwrap();
        let mut pass = crate::ellipsis_elimination::EllipsisElimination::new(&types, &premises, 2);
        super::visit_forest(&mut pass, POSITIVE, &mut main, &mut conditions);
        assert_eq!(pass.finish().unwrap(), 1);
        super::resolve_forest(&types, &rules, POSITIVE, &mut main, &mut conditions).unwrap();
        super::validate_forest(&rules, &main, &conditions).unwrap();
    }

    #[test]
    fn unsupported_ellipsis_is_a_structured_preparation_error() {
        assert!(matches!(prepare_with_givens(r"\ldots", &[]),
            Err(crate::type_resolver::TypeError::Ellipsis(error))
                if *error == crate::ellipsis_elimination::EllipsisEliminationError::UnsupportedPattern));
    }
}
