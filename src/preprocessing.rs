use std::collections::HashMap;

use crate::{
    Expr,
    logic_lowering::LogicLowering,
    operator_visitors::{Norm2SquaredVisitor, Norm2Visitor, SquareRootVisitor},
    type_resolver::{OperatorTypeRules, TypeError, TypeLookup, TypeResolver, TypedMetadata},
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
    let standard_rules = OperatorTypeRules::standard();
    TypeResolver::new(types, &standard_rules).resolve(&mut expression, context)?;
    LogicLowering.visit_expr_mut(context, &mut expression);
    let mut norm2_squared = Norm2SquaredVisitor::default();
    norm2_squared.visit_expr_mut(context, &mut expression);
    norm2_squared.finish()?;
    let mut norm2 = Norm2Visitor::default();
    norm2.visit_expr_mut(context, &mut expression);
    let mut side_conditions = norm2.finish()?;
    let mut square_roots = SquareRootVisitor::default();
    square_roots.visit_expr_mut(context, &mut expression);
    for condition in &mut side_conditions {
        for assertion in &mut condition.defining_assertions {
            square_roots.visit_expr_mut(context, assertion);
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                square_roots.visit_expr_mut(context, assertion);
            }
        }
    }
    side_conditions.extend(square_roots.finish()?);

    let synthetic_types = side_conditions
        .iter()
        .map(|condition| {
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
    let core_rules = OperatorTypeRules::core();
    TypeResolver::new(&extended_types, &core_rules).resolve(&mut expression, context)?;
    for condition in &mut side_conditions {
        for assertion in &mut condition.defining_assertions {
            TypeResolver::new(&extended_types, &core_rules).resolve(assertion, context)?;
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                TypeResolver::new(&extended_types, &core_rules).resolve(assertion, context)?;
            }
        }
    }
    Ok(PreparedExpression {
        expression,
        side_conditions,
        context,
    })
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
        Cmp, Expr, Finop, RawExpr, TypeExpr,
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
    fn later_visitors_process_conditions_generated_by_norm_lowering() {
        let prepared = prepare(
            r"\left\lVert A^{\frac{1}{2}} \right\rVert_{2}",
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
}
