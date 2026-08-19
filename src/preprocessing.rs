use crate::{
    Expr,
    logic_lowering::LogicLowering,
    operator_visitors::SquareRootVisitor,
    type_resolver::{TypeError, TypeLookup, TypeResolver, TypedMetadata},
    visit_mut::{SideCondition, VisitContext, VisitMut},
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
    TypeResolver::new(types).resolve(&mut expression, context)?;
    LogicLowering.visit_expr_mut(context, &mut expression);
    let mut square_roots = SquareRootVisitor::default();
    square_roots.visit_expr_mut(context, &mut expression);
    let side_conditions = square_roots.finish()?;
    Ok(PreparedExpression {
        expression,
        side_conditions,
        context,
    })
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::prepare_expression;
    use crate::{Expr, from_tex, type_resolver::SymbolicTypeEnvironment, visit_mut::VisitContext};

    #[test]
    fn implicit_constant_roots_have_distinct_internal_names_and_common_display_names() {
        let parsed: Expr<()> =
            from_tex::expr(&parse(r"\mathbb{0}^{\frac{1}{2}} + \mathbb{0}^{\frac{1}{2}}").unwrap())
                .unwrap();
        let prepared = prepare_expression(
            &SymbolicTypeEnvironment::default(),
            &parsed,
            VisitContext {
                logical_polarity: true,
            },
        )
        .unwrap();
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
}
