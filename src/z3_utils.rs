use std::collections::BTreeMap;

use z3::ast::{Ast, Bool, Int};

use crate::{
    Binop, Cmp, Expr, Finop, Monop, NaturalEvaluationError, NaturalParameter, RawExpr, visit::Visit,
};

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

pub(crate) fn lower_natural_with<Metadata>(
    expression: &Expr<Metadata>,
    resolve: &mut impl FnMut(&NaturalParameter) -> Result<Int, NaturalEvaluationError>,
) -> Result<Int, NaturalEvaluationError> {
    lower_natural_scoped_with(expression, resolve, &mut |depth| {
        Err(NaturalEvaluationError::UnboundNatural(depth))
    })
}

pub(crate) fn lower_natural_scoped_with<Metadata>(
    expression: &Expr<Metadata>,
    resolve: &mut impl FnMut(&NaturalParameter) -> Result<Int, NaturalEvaluationError>,
    resolve_bound: &mut impl FnMut(usize) -> Result<Int, NaturalEvaluationError>,
) -> Result<Int, NaturalEvaluationError> {
    match &expression.raw {
        RawExpr::NatLiteral(value) => Ok(Int::from_u64(*value)),
        RawExpr::Variable(variable) => resolve(&NaturalParameter::Variable(variable.clone())),
        RawExpr::ImplicitDimension(dimension) => {
            resolve(&NaturalParameter::ImplicitDimension(*dimension))
        }
        RawExpr::BoundNatural(depth) => resolve_bound(*depth),
        RawExpr::Finop(Finop::Plus, terms) => {
            let mut terms = terms.iter();
            let first = terms
                .next()
                .ok_or(NaturalEvaluationError::EmptyOperation("addition"))?;
            terms.try_fold(
                lower_natural_scoped_with(first, resolve, resolve_bound)?,
                |sum, term| Ok(sum + lower_natural_scoped_with(term, resolve, resolve_bound)?),
            )
        }
        RawExpr::Finop(Finop::Times, factors) => {
            let mut factors = factors.iter();
            let first = factors
                .next()
                .ok_or(NaturalEvaluationError::EmptyOperation("multiplication"))?;
            factors.try_fold(
                lower_natural_scoped_with(first, resolve, resolve_bound)?,
                |product, factor| {
                    Ok(product * lower_natural_scoped_with(factor, resolve, resolve_bound)?)
                },
            )
        }
        RawExpr::Monop(Monop::Neg, inner) => {
            Ok(-lower_natural_scoped_with(inner, resolve, resolve_bound)?)
        }
        _ => Err(NaturalEvaluationError::UnsupportedSyntax(
            "unsupported natural expression",
        )),
    }
}

pub(crate) fn evaluate_natural<Metadata>(
    expression: &Expr<Metadata>,
    assignment: &std::collections::HashMap<NaturalParameter, u64>,
) -> Result<u64, NaturalEvaluationError> {
    lower_natural_with(expression, &mut |parameter| {
        assignment
            .get(parameter)
            .copied()
            .map(Int::from_u64)
            .ok_or_else(|| NaturalEvaluationError::MissingAssignment(parameter.clone()))
    })?
    .simplify()
    .as_u64()
    .ok_or(NaturalEvaluationError::Overflow)
}

pub(crate) fn evaluate_natural_with_context<Metadata>(
    expression: &Expr<Metadata>,
    assignment: &std::collections::HashMap<NaturalParameter, u64>,
    locals: &[(crate::Variable, u64)],
    bound_values: &[u64],
) -> Result<u64, NaturalEvaluationError> {
    lower_natural_scoped_with(
        expression,
        &mut |parameter| {
            if let NaturalParameter::Variable(variable) = parameter
                && let Some((_, value)) = locals.iter().rev().find(|(found, _)| found == variable)
            {
                return Ok(Int::from_u64(*value));
            }
            assignment
                .get(parameter)
                .copied()
                .map(Int::from_u64)
                .ok_or_else(|| NaturalEvaluationError::MissingAssignment(parameter.clone()))
        },
        &mut |depth| {
            bound_values
                .iter()
                .rev()
                .nth(depth)
                .copied()
                .map(Int::from_u64)
                .ok_or(NaturalEvaluationError::UnboundNatural(depth))
        },
    )?
    .simplify()
    .as_u64()
    .ok_or(NaturalEvaluationError::Overflow)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PresburgerClassification {
    Valid,
    NotNatural,
    Unsupported(&'static str),
}

pub(crate) fn classify_presburger<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
) -> PresburgerClassification {
    let mut validator = PresburgerValidator {
        natural_symbols,
        classification: PresburgerClassification::NotNatural,
    };
    validator.visit_expr(expression);
    validator.classification
}

struct PresburgerValidator<'a> {
    natural_symbols: &'a BTreeMap<NaturalParameter, Int>,
    classification: PresburgerClassification,
}

impl<Metadata> Visit<Metadata> for PresburgerValidator<'_> {
    fn visit_expr(&mut self, expression: &Expr<Metadata>) {
        self.classification = classify_node(expression, self.natural_symbols);
    }
}

fn classify_node<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
) -> PresburgerClassification {
    match &expression.raw {
        RawExpr::NatLiteral(_) => PresburgerClassification::Valid,
        RawExpr::ImplicitDimension(dimension)
            if natural_symbols.contains_key(&NaturalParameter::ImplicitDimension(*dimension)) =>
        {
            PresburgerClassification::Valid
        }
        RawExpr::ImplicitDimension(_) => PresburgerClassification::NotNatural,
        RawExpr::BoundNatural(_) => PresburgerClassification::NotNatural,
        RawExpr::Variable(variable)
            if natural_symbols.contains_key(&NaturalParameter::Variable(variable.clone())) =>
        {
            PresburgerClassification::Valid
        }
        RawExpr::Variable(_) => PresburgerClassification::NotNatural,
        RawExpr::Monop(Monop::Neg, inner) => classify_node(inner, natural_symbols),
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
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
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
    use crate::{Binop, Expr, Finop, Monop, NaturalParameter, RawExpr, Variable};

    fn variable(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    #[test]
    fn classifies_the_supported_presburger_subset() {
        let n = Variable::new("n");
        let symbols = BTreeMap::from([(
            NaturalParameter::Variable(n.clone()),
            Int::new_const(n.z3_name()),
        )]);
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
        assert_eq!(
            classify_presburger(&negated, &symbols),
            PresburgerClassification::Valid
        );

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
