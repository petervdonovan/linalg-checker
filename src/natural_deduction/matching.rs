use super::*;
use crate::unification::Unifier;

#[derive(Clone, Debug, Default)]
pub(crate) struct Match {
    pub assignments: BTreeMap<Variable, Expr<()>>,
    pub nonce_pairs: BTreeSet<(ImplicitDimension, ImplicitDimension)>,
    pub premises: Vec<ProofInput>,
    pub supporting_facts: Vec<Expr<()>>,
}

pub(crate) fn match_expression(
    pattern: &Expr<()>,
    candidate: &Expr<()>,
    binders: &BTreeSet<Variable>,
    accessible: &BTreeSet<Variable>,
    state: &Match,
) -> Option<Match> {
    let mut unifier = Unifier {
        metavariables: binders,
        assignments: state.assignments.clone(),
        pattern_accessible: accessible.iter().chain(binders).cloned().collect(),
        candidate_accessible: accessible.clone(),
        pattern_bound: BTreeSet::new(),
        candidate_bound: BTreeSet::new(),
        bound_forward: BTreeMap::new(),
        bound_reverse: BTreeMap::new(),
        nonce_pairs: state.nonce_pairs.clone(),
    };
    if !unifier.expression(pattern, candidate) {
        return None;
    }
    Some(Match {
        assignments: unifier.assignments,
        nonce_pairs: unifier.nonce_pairs,
        ..state.clone()
    })
}

pub(crate) fn views(context: &ProofContext) -> Vec<(Premise, Expr<()>)> {
    let mut result = Vec::new();
    for fact in &context.facts {
        for derivation in &fact.derivations {
            for (alternative, expression) in std::iter::once((None, fact.formula.analyzed())).chain(
                fact.alternatives
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (Some(i), e.analyzed())),
            ) {
                for (conjunct, _expression) in conjunction_views(expression).into_iter().enumerate()
                {
                    let premise = Premise {
                        fact: fact.id,
                        derivation: derivation.id,
                        assumption: match derivation.proof {
                            NaturalDeductionProof::Assumption { assumption } => Some(assumption),
                            _ => None,
                        },
                        expression: fact.expression.clone(),
                        alternative,
                        conjunct,
                    };
                    let normalized = context
                        .analyzed_view(&premise)
                        .expect("visible views are checked")
                        .with_default_metadata();
                    result.push((premise, normalized));
                }
            }
        }
    }
    result
}

pub(crate) fn match_requirements(
    context: &ProofContext,
    binders: &BTreeSet<Variable>,
    requirements: &[&Expr<()>],
    initial: Match,
) -> Vec<Match> {
    match_views(context, binders, requirements, initial, views(context))
}

pub(crate) fn match_assumption_requirements(
    context: &ProofContext,
    binders: &BTreeSet<Variable>,
    requirements: &[&Expr<()>],
    initial: Match,
) -> Vec<Match> {
    let assumptions = views(context)
        .into_iter()
        .filter(|(p, _)| {
            context
                .derivation(p.derivation)
                .is_some_and(|d| matches!(d.proof, NaturalDeductionProof::Assumption { .. }))
        })
        .collect();
    match_views(context, binders, requirements, initial, assumptions)
}

/// Matches context views and conjunction assembly only; never invokes rule search.
fn match_one(
    context: &ProofContext,
    binders: &BTreeSet<Variable>,
    requirement: &Expr<()>,
    state: &Match,
    available: &[(Premise, Expr<()>)],
) -> Vec<Match> {
    let accessible = context.types.types.keys().cloned().collect();
    let mut result = Vec::new();
    for (premise, expression) in available {
        if binders.is_empty() && requirement != expression {
            continue;
        }
        if let Some(mut matched) =
            match_expression(requirement, expression, binders, &accessible, state)
        {
            matched
                .premises
                .push(super::proof::view_input(context, premise));
            let fact = context.facts.iter().find(|f| f.id == premise.fact).unwrap();
            let supporting = premise
                .alternative
                .map(|i| &fact.alternatives[i])
                .unwrap_or(&fact.formula)
                .meaning();
            if !matched.supporting_facts.contains(&supporting) {
                matched.supporting_facts.push(supporting);
            }
            result.push(matched);
        }
    }
    if let RawExpr::Finop(Finop::And, operands) = &requirement.raw
        && !operands.is_empty()
    {
        let offset = state.premises.len();
        let mut states = vec![state.clone()];
        for operand in operands {
            states = states
                .iter()
                .flat_map(|s| match_one(context, binders, operand, s, available))
                .collect();
        }
        for mut matched in states {
            let premises = matched.premises.split_off(offset);
            let conclusion =
                crate::formula::substitute_free_variables(requirement, &matched.assignments);
            matched.premises.push(ProofInput::local(
                conclusion,
                NaturalDeductionProof::ConjunctionIntroduction { premises },
            ));
            result.push(matched);
        }
    }
    result
}
fn match_views(
    context: &ProofContext,
    binders: &BTreeSet<Variable>,
    requirements: &[&Expr<()>],
    initial: Match,
    views: Vec<(Premise, Expr<()>)>,
) -> Vec<Match> {
    let mut states = vec![initial];
    for requirement in requirements {
        states = states
            .iter()
            .flat_map(|s| match_one(context, binders, requirement, s, &views))
            .collect();
        if states.is_empty() {
            break;
        }
    }
    states
}
