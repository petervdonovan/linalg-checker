use super::*;
use crate::unification::Unifier;

#[derive(Clone, Debug, Default)]
pub(crate) struct Match {
    pub assignments: BTreeMap<Variable, Expr<()>>,
    pub nonce_pairs: BTreeSet<(ImplicitDimension, ImplicitDimension)>,
    pub premises: Vec<Premise>,
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
            for (alternative, expression) in std::iter::once((None, &fact.expression)).chain(
                fact.alternatives
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (Some(i), e)),
            ) {
                for (conjunct, expression) in conjunction_views(expression).into_iter().enumerate()
                {
                    let premise = Premise {
                        fact: fact.id,
                        derivation: derivation.id,
                        expression: fact.expression.clone(),
                        alternative,
                        conjunct,
                    };
                    let normalized = context
                        .analyzed_view(&premise)
                        .map(|e| e.with_default_metadata())
                        .unwrap_or_else(|| expression.clone());
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

fn match_views(
    context: &ProofContext,
    binders: &BTreeSet<Variable>,
    requirements: &[&Expr<()>],
    initial: Match,
    views: Vec<(Premise, Expr<()>)>,
) -> Vec<Match> {
    let accessible = context.types.types.keys().cloned().collect();
    let mut states = vec![initial];
    for requirement in requirements {
        let mut next = Vec::new();
        for state in &states {
            for (premise, expression) in &views {
                if let Some(mut matched) =
                    match_expression(requirement, expression, binders, &accessible, state)
                {
                    if !matched.premises.contains(premise) {
                        matched.premises.push(premise.clone());
                    }
                    let fact = context.facts.iter().find(|f| f.id == premise.fact).unwrap();
                    let supporting = premise
                        .alternative
                        .map(|i| &fact.alternatives[i])
                        .unwrap_or(&fact.expression);
                    if !matched.supporting_facts.contains(supporting) {
                        matched.supporting_facts.push(supporting.clone());
                    }
                    next.push(matched);
                }
            }
        }
        states = next;
        if states.is_empty() {
            break;
        }
    }
    states
}
