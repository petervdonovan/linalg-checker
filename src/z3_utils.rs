use std::collections::BTreeMap;

use z3::ast::{Bool, Int};

use crate::{Binop, Cmp, Expr, Finop, Monop, RawExpr, Variable, visit::Visit};

pub(crate) fn compare_int(left: &Int, comparison: Cmp, right: &Int) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Ne => left.eq(right).not(),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PresburgerClassification {
    Valid,
    NotNatural,
    Unsupported(&'static str),
}

pub(crate) fn classify_presburger<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<Variable, Int>,
) -> PresburgerClassification {
    let mut validator = PresburgerValidator {
        natural_symbols,
        classification: PresburgerClassification::NotNatural,
    };
    validator.visit_expr(expression);
    validator.classification
}

struct PresburgerValidator<'a> {
    natural_symbols: &'a BTreeMap<Variable, Int>,
    classification: PresburgerClassification,
}

impl<Metadata> Visit<Metadata> for PresburgerValidator<'_> {
    fn visit_expr(&mut self, expression: &Expr<Metadata>) {
        self.classification = classify_node(expression, self.natural_symbols);
    }
}

fn classify_node<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<Variable, Int>,
) -> PresburgerClassification {
    match &expression.raw {
        RawExpr::NatLiteral(_) => PresburgerClassification::Valid,
        RawExpr::Variable(variable) if natural_symbols.contains_key(variable) => {
            PresburgerClassification::Valid
        }
        RawExpr::Variable(_) => PresburgerClassification::NotNatural,
        RawExpr::Monop(Monop::Neg, inner) => match classify_node(inner, natural_symbols) {
            PresburgerClassification::Valid => {
                PresburgerClassification::Unsupported("natural expressions do not support negation")
            }
            classification => classification,
        },
        RawExpr::Finop(Finop::Plus, terms) => {
            classify_terms(terms, natural_symbols, "natural addition cannot be empty")
        }
        RawExpr::Finop(Finop::Times, factors) => {
            let classification = classify_terms(
                factors,
                natural_symbols,
                "natural multiplication cannot be empty",
            );
            if classification == PresburgerClassification::Valid
                && factors
                    .iter()
                    .filter(|factor| !matches!(factor.raw, RawExpr::NatLiteral(_)))
                    .count()
                    > 1
            {
                PresburgerClassification::Unsupported(
                    "symbolic multiplication is not Presburger arithmetic",
                )
            } else {
                classification
            }
        }
        RawExpr::Binop(Binop::Div, left, right) => match (
            classify_node(left, natural_symbols),
            classify_node(right, natural_symbols),
        ) {
            (PresburgerClassification::Valid, PresburgerClassification::Valid) => {
                PresburgerClassification::Unsupported(
                    "natural division is not Presburger arithmetic",
                )
            }
            (PresburgerClassification::NotNatural, _)
            | (_, PresburgerClassification::NotNatural) => PresburgerClassification::NotNatural,
            (PresburgerClassification::Unsupported(message), _)
            | (_, PresburgerClassification::Unsupported(message)) => {
                PresburgerClassification::Unsupported(message)
            }
        },
        _ => PresburgerClassification::NotNatural,
    }
}

fn classify_terms<Metadata>(
    terms: &[Expr<Metadata>],
    natural_symbols: &BTreeMap<Variable, Int>,
    empty_message: &'static str,
) -> PresburgerClassification {
    if terms.is_empty() {
        return PresburgerClassification::Unsupported(empty_message);
    }
    let mut unsupported = None;
    for term in terms {
        match classify_node(term, natural_symbols) {
            PresburgerClassification::Valid => {}
            PresburgerClassification::NotNatural => {
                return PresburgerClassification::NotNatural;
            }
            PresburgerClassification::Unsupported(message) => unsupported = Some(message),
        }
    }
    unsupported.map_or(
        PresburgerClassification::Valid,
        PresburgerClassification::Unsupported,
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use z3::ast::Int;

    use super::{PresburgerClassification, classify_presburger};
    use crate::{Binop, Expr, Finop, Monop, RawExpr, Variable};

    fn variable(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    #[test]
    fn classifies_the_supported_presburger_subset() {
        let n = Variable::new("n");
        let symbols = BTreeMap::from([(n.clone(), Int::new_const(n.z3_name()))]);
        let linear = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::NatLiteral(1)),
                Expr::new(RawExpr::Finop(
                    Finop::Times,
                    vec![Expr::new(RawExpr::NatLiteral(2)), variable("n")],
                )),
            ],
        ));
        assert_eq!(
            classify_presburger(&linear, &symbols),
            PresburgerClassification::Valid
        );

        let nonlinear = Expr::new(RawExpr::Finop(
            Finop::Times,
            vec![variable("n"), variable("n")],
        ));
        assert!(matches!(
            classify_presburger(&nonlinear, &symbols),
            PresburgerClassification::Unsupported(_)
        ));

        let negated = Expr::new(RawExpr::Monop(Monop::Neg, variable("n")));
        assert!(matches!(
            classify_presburger(&negated, &symbols),
            PresburgerClassification::Unsupported(_)
        ));

        let divided = Expr::new(RawExpr::Binop(
            Binop::Div,
            variable("n"),
            Expr::new(RawExpr::NatLiteral(2)),
        ));
        assert!(matches!(
            classify_presburger(&divided, &symbols),
            PresburgerClassification::Unsupported(_)
        ));

        assert_eq!(
            classify_presburger(&variable("x"), &symbols),
            PresburgerClassification::NotNatural
        );
    }
}
