//! Rewrite pass over expressions that eliminates ellipses using program synthesis.
//!
//! The visitor intentionally preserves ellipses until synthesis is implemented.

use crate::{
    Environment, Expr,
    deep_clone::deep_clone,
    visit_mut::{VisitContext, VisitMut},
};

/// Environment-backed ellipsis rewrite pass.
///
/// This currently performs only the default recursive traversal. Keeping the
/// environment in the visitor establishes the interface needed by the future
/// synthesis implementation without assigning placeholder semantics to an
/// ellipsis.
pub struct EllipsisElimination<'a> {
    _environment: &'a Environment,
}

impl<'a> EllipsisElimination<'a> {
    pub fn new(environment: &'a Environment) -> Self {
        Self {
            _environment: environment,
        }
    }
}

impl<Metadata> VisitMut<Metadata> for EllipsisElimination<'_> {}

pub fn eliminate_ellipses<Metadata: Clone>(
    environment: &Environment,
    expression: &Expr<Metadata>,
) -> Expr<Metadata> {
    let mut rewritten = deep_clone(expression);
    EllipsisElimination::new(environment).visit_expr_mut(VisitContext::positive(), &mut rewritten);
    rewritten
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::eliminate_ellipses;
    use crate::{
        Environment, Expr, Finop, RawExpr,
        elaboration::{ElaborationError, elaborate},
        from_tex,
        preprocessing::PreparedExpression,
        type_resolver::TypedMetadata,
        visit::{self, Visit},
        visit_mut::{VisitContext, VisitMut},
    };

    #[test]
    fn identity_elimination_preserves_ellipses_in_a_unique_tree() {
        let original: Expr<()> = from_tex::expr(&parse(r"1, \ldots, n").unwrap()).unwrap();
        let mut rewritten = eliminate_ellipses(&Environment::default(), &original);
        let rewritten_node = rewritten
            .get_mut()
            .expect("rewritten root should be uniquely owned");
        let RawExpr::Finop(Finop::SeqLiteral, elements) = &mut rewritten_node.raw else {
            panic!("expected a sequence literal")
        };
        assert!(
            elements
                .iter()
                .any(|element| matches!(element.raw, RawExpr::Ellipsis))
        );
        assert!(
            elements
                .iter_mut()
                .all(|element| element.get_mut().is_some())
        );
        assert_eq!(original.as_latex().to_string(), r"1, \ldots, n");
    }

    #[test]
    fn immutable_and_mutable_visitors_expose_ellipsis_hooks() {
        struct ImmutableCounter(usize);
        impl Visit<()> for ImmutableCounter {
            fn visit_raw_expr_ellipsis(&mut self) {
                self.0 += 1;
                visit::visit_raw_expr_ellipsis(self);
            }
        }
        struct MutableCounter(usize);
        impl VisitMut<()> for MutableCounter {
            fn visit_raw_expr_ellipsis_mut(&mut self, _context: VisitContext) {
                self.0 += 1;
            }
        }

        let expression = Expr::new(RawExpr::Finop(
            Finop::SeqLiteral,
            vec![Expr::new(RawExpr::Ellipsis), Expr::new(RawExpr::Ellipsis)],
        ));
        let mut immutable = ImmutableCounter(0);
        immutable.visit_expr(&expression);
        assert_eq!(immutable.0, 2);

        let mut expression = expression.with_default_metadata();
        let mut mutable = MutableCounter(0);
        mutable.visit_expr_mut(VisitContext::positive(), &mut expression);
        assert_eq!(mutable.0, 2);
    }

    #[test]
    fn concrete_elaboration_rejects_an_uneliminated_ellipsis() {
        let prepared = PreparedExpression {
            expression: Expr::with_metadata(TypedMetadata::default(), RawExpr::Ellipsis),
            side_conditions: Vec::new(),
            context: VisitContext::positive(),
        };
        assert!(matches!(
            elaborate(&Environment::default(), &prepared),
            Err(ElaborationError::Unsupported(
                "ellipses must be eliminated before Z3 lowering"
            ))
        ));
    }
}
