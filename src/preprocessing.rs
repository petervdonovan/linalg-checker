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

pub fn prepare_expression<Metadata, Lookup: TypeLookup>(
    types: &Lookup,
    expression: &Expr<Metadata>,
    context: VisitContext,
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
            context,
            &mut expression,
            &mut side_conditions,
        )?;

        let mut rewrites = 0;
        let mut logic = LogicLowering::default();
        visit_forest(&mut logic, context, &mut expression, &mut side_conditions);
        rewrites += logic.rewrites();

        let mut norm2_squared = Norm2SquaredVisitor::default();
        visit_forest(
            &mut norm2_squared,
            context,
            &mut expression,
            &mut side_conditions,
        );
        rewrites += norm2_squared.finish()?;

        let mut norm2 = Norm2Visitor::default();
        visit_forest(&mut norm2, context, &mut expression, &mut side_conditions);
        let (norm_rewrites, conditions) = norm2.finish()?;
        rewrites += norm_rewrites;
        merge_side_conditions(&mut side_conditions, conditions);

        let mut square_roots = SquareRootVisitor::default();
        visit_forest(
            &mut square_roots,
            context,
            &mut expression,
            &mut side_conditions,
        );
        let (root_rewrites, conditions) = square_roots.finish()?;
        rewrites += root_rewrites;
        merge_side_conditions(&mut side_conditions, conditions);

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
    visitor.visit_expr_mut(context, expression);
    for condition in side_conditions {
        for assertion in &mut condition.defining_assertions {
            visitor.visit_expr_mut(context, assertion);
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                visitor.visit_expr_mut(context, assertion);
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
    TypeResolver::new(types, rules).resolve(expression, context)?;
    for condition in side_conditions {
        for assertion in &mut condition.defining_assertions {
            TypeResolver::new(types, rules).resolve(assertion, context)?;
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                TypeResolver::new(types, rules).resolve(assertion, context)?;
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
}
