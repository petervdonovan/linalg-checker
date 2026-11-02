pub(super) enum RuleResult {
    Established(Vec<super::Derivation>),
    NoMatch,
    Inconclusive(Vec<String>),
}
use super::matching::{match_expression, views};
use super::*;

fn derived(
    context: &ProofContext,
    proof: NaturalDeductionProof,
    premises: &[Premise],
) -> Derivation {
    let mut result = Derivation::new(proof);
    for premise in premises {
        let d = context
            .derivation(premise.derivation)
            .expect("context premise has a derivation");
        result.assumptions.extend(&d.assumptions);
        result
            .required_variables
            .extend(d.required_variables.iter().cloned());
        result.required_scopes.extend(&d.required_scopes);
    }
    result
}
fn with_side_conditions(
    context: &ProofContext,
    mut derivation: Derivation,
    checks: &impl SideConditionChecker,
) -> Derivation {
    for id in checks.premise_derivations() {
        let premise = context
            .derivation(*id)
            .expect("side-condition evidence belongs to this context");
        derivation.assumptions.extend(&premise.assumptions);
        derivation
            .required_variables
            .extend(premise.required_variables.iter().cloned());
        derivation.required_scopes.extend(&premise.required_scopes);
        derivation.side_condition_premises.push(*id);
    }
    derivation
}
fn side_conditions(
    checks: &mut impl SideConditionChecker,
    spec: &QuantifierSpec,
    state: &Match,
    reasons: &mut Vec<String>,
) -> bool {
    if !spec
        .introduced
        .iter()
        .all(|v| state.assignments.contains_key(v))
    {
        return false;
    }
    match checks.check_instantiation(
        spec,
        &state.assignments,
        &state.nonce_pairs,
        &state.supporting_facts,
    ) {
        SideConditionResult::Valid => true,
        SideConditionResult::Invalid => false,
        SideConditionResult::Inconclusive(reason) => {
            if !reasons.contains(&reason) {
                reasons.push(reason);
            }
            false
        }
    }
}
fn requirements(spec: &QuantifierSpec) -> Vec<&Expr<()>> {
    spec.premises
        .iter()
        .filter(|p| !spec.is_binder_declaration(p))
        .collect()
}

// Discharging every matching occurrence dominates discharging a subset: it
// produces the same formula with fewer dependencies and does not close scopes.
// Conjunctions also discharge their individual constituent assumptions.
fn discharge_sets(context: &ProofContext, expression: &Expr<()>) -> Vec<BTreeSet<AssumptionId>> {
    let views = conjunction_views(expression);
    let discharged = context
        .assumptions
        .values()
        .filter(|a| views.contains(&&a.expression))
        .map(|a| a.id)
        .collect::<BTreeSet<_>>();
    if discharged.is_empty() {
        vec![BTreeSet::new()]
    } else {
        vec![BTreeSet::new(), discharged]
    }
}
fn substituted(expression: &Expr<()>, assignments: &BTreeMap<Variable, Expr<()>>) -> Expr<()> {
    crate::formula::substitute_free_variables(expression, assignments)
}

pub(super) fn check(
    context: &ProofContext,
    conclusion: &Expr<()>,
    conclusion_free: &BTreeSet<Variable>,
    conclusion_spec: Option<&QuantifierSpec>,
    checks: &mut impl SideConditionChecker,
) -> RuleResult {
    let mut results = Vec::new();
    let mut reasons = Vec::new();
    let available = views(context);
    let accessible = context.types.types.keys().cloned().collect::<BTreeSet<_>>();

    for (premise, expression) in &available {
        if expression == conclusion {
            results.push(derived(
                context,
                NaturalDeductionProof::Reuse {
                    premise: premise.clone(),
                    exact: false,
                },
                std::slice::from_ref(premise),
            ));
        }
    }

    if let Some(spec) = conclusion_spec {
        match spec.kind {
            QuantifierKind::Exists => {
                let mut required = requirements(spec);
                required.push(&spec.body);
                for state in
                    match_requirements(context, &spec.introduced, &required, Match::default())
                {
                    if side_conditions(checks, spec, &state, &mut reasons) {
                        results.push(with_side_conditions(
                            context,
                            derived(
                                context,
                                NaturalDeductionProof::ExistentialIntroduction {
                                    premises: state.premises.clone(),
                                    assignments: state.assignments,
                                },
                                &state.premises,
                            ),
                            checks,
                        ));
                    }
                }
            }
            QuantifierKind::Forall => {
                for (premise, expression) in &available {
                    let Some(state) = match_expression(
                        &spec.body,
                        expression,
                        &spec.introduced,
                        &accessible,
                        &Match::default(),
                    ) else {
                        continue;
                    };
                    // Restrictions may provide parameters absent from the body.
                    // Only assumptions are eligible to be discharged here.
                    // Unused restrictions can be discharged vacuously. Matching
                    // declarations also finds arbitrary parameters absent from the body.
                    let mut restriction_matches = vec![state];
                    for restriction in &spec.premises {
                        let mut next = restriction_matches.clone();
                        for state in restriction_matches {
                            next.extend(super::matching::match_assumption_requirements(
                                context,
                                &spec.introduced,
                                &[restriction],
                                state,
                            ));
                        }
                        restriction_matches = next;
                    }
                    for mut matched in restriction_matches {
                        matched.supporting_facts.push((*expression).clone());
                        if !side_conditions(checks, spec, &matched, &mut reasons) {
                            continue;
                        }
                        let Some(assignments) = matched
                            .assignments
                            .iter()
                            .map(|(v, e)| match &e.raw {
                                RawExpr::Variable(p)
                                    if context.parameters.get(p).is_some_and(|p| !p.witness) =>
                                {
                                    Some((v.clone(), p.clone()))
                                }
                                _ => None,
                            })
                            .collect::<Option<BTreeMap<_, _>>>()
                        else {
                            continue;
                        };
                        let parameters = assignments.values().cloned().collect::<BTreeSet<_>>();
                        if parameters.len() != assignments.len() {
                            continue;
                        }
                        let mut choices = vec![BTreeSet::new()];
                        for restriction in &spec.premises {
                            let instance = substituted(restriction, &matched.assignments);
                            let alternatives = discharge_sets(context, &instance);
                            choices = choices
                                .iter()
                                .flat_map(|a| {
                                    alternatives
                                        .iter()
                                        .map(move |b| a.union(b).copied().collect())
                                })
                                .collect();
                        }
                        for discharged in choices {
                            let d = derived(
                                context,
                                NaturalDeductionProof::UniversalIntroduction {
                                    premise: premise.clone(),
                                    assignments: assignments.clone(),
                                    discharged: discharged.clone(),
                                },
                                std::slice::from_ref(premise),
                            );
                            let mut d = with_side_conditions(context, d, checks);
                            d.assumptions.retain(|a| !discharged.contains(a));
                            if !context
                                .dependency_variables(&d.assumptions)
                                .is_disjoint(&parameters)
                            {
                                continue;
                            }
                            d.required_variables.retain(|v| !parameters.contains(v));
                            context.refresh_scopes(&mut d, conclusion_free);
                            // A type dependency may reintroduce a generalized parameter.
                            if !d.required_variables.is_disjoint(&parameters) {
                                continue;
                            }
                            results.push(d);
                        }
                    }
                }
            }
        }
    }

    let unbound = free_variables(std::iter::once(conclusion))
        .difference(&accessible)
        .cloned()
        .collect::<BTreeSet<_>>();
    for (source, _expression) in &available {
        let checked_view = context
            .analyzed_view(source)
            .expect("visible premises have checked binding analysis");
        let spec = QuantifierSpec::from_analyzed(&checked_view);
        let Ok(spec) = spec else {
            continue;
        };
        match spec.kind {
            QuantifierKind::Forall if unbound.is_empty() => {
                let Some(state) = match_expression(
                    &spec.body,
                    conclusion,
                    &spec.introduced,
                    &accessible,
                    &Match::default(),
                ) else {
                    continue;
                };
                for mut state in
                    match_requirements(context, &spec.introduced, &requirements(&spec), state)
                {
                    state.supporting_facts.push(conclusion.clone());
                    if !side_conditions(checks, &spec, &state, &mut reasons) {
                        continue;
                    }
                    let mut premises = state.premises.clone();
                    premises.push(source.clone());
                    results.push(with_side_conditions(
                        context,
                        derived(
                            context,
                            NaturalDeductionProof::UniversalElimination {
                                source: source.clone(),
                                premises: state.premises,
                                assignments: state.assignments,
                            },
                            &premises,
                        ),
                        checks,
                    ));
                }
            }
            QuantifierKind::Exists if !unbound.is_empty() => {
                let mut payload = requirements(&spec).into_iter().cloned().collect::<Vec<_>>();
                payload.push(spec.body.clone());
                let payload = if payload.len() == 1 {
                    payload.pop().unwrap()
                } else {
                    Expr::new(RawExpr::Finop(Finop::And, payload))
                };
                for pattern in conjunction_views(&payload) {
                    let Some(state) = match_expression(
                        pattern,
                        conclusion,
                        &spec.introduced,
                        &accessible,
                        &Match::default(),
                    ) else {
                        continue;
                    };
                    if !spec
                        .introduced
                        .iter()
                        .all(|v| state.assignments.contains_key(v))
                    {
                        continue;
                    }
                    let Some(assignments) = state
                        .assignments
                        .iter()
                        .map(|(v, e)| match &e.raw {
                            RawExpr::Variable(p) if unbound.contains(p) => {
                                Some((v.clone(), p.clone()))
                            }
                            _ => None,
                        })
                        .collect::<Option<BTreeMap<_, _>>>()
                    else {
                        continue;
                    };
                    let variables = assignments.values().cloned().collect::<BTreeSet<_>>();
                    if variables != unbound || variables.len() != assignments.len() {
                        continue;
                    }
                    let introduced_types = assignments
                        .iter()
                        .map(|(binder, candidate)| {
                            let ty = Expr::new(RawExpr::Type(spec.bindings[binder].clone()));
                            let RawExpr::Type(ref ty) = substituted(&ty, &state.assignments).raw
                            else {
                                unreachable!()
                            };
                            (candidate.clone(), ty.clone())
                        })
                        .collect();
                    // Renaming fresh variables is type preserving. The validator
                    // subsequently checks/lower the payload with these types.
                    results.push(derived(
                        context,
                        NaturalDeductionProof::ExistentialElimination {
                            source: source.clone(),
                            assignments,
                            introduced_types,
                        },
                        std::slice::from_ref(source),
                    ));
                }
            }
            _ => {}
        }
    }

    if unbound.is_empty()
        && let RawExpr::LogicChain(chain) = &conclusion.raw
        && let [(Logic::Imp, consequent)] = chain.assertions.as_slice()
    {
        for (premise, expression) in &available {
            if expression != consequent {
                continue;
            }
            for discharged in discharge_sets(context, &chain.start) {
                let mut d = derived(
                    context,
                    NaturalDeductionProof::ImplicationIntroduction {
                        premise: premise.clone(),
                        discharged: discharged.clone(),
                    },
                    std::slice::from_ref(premise),
                );
                d.assumptions.retain(|a| !discharged.contains(a));
                results.push(d);
            }
        }
    }
    let mut nondominated: Vec<Derivation> = Vec::new();
    for mut result in results {
        context.refresh_scopes(&mut result, conclusion_free);
        result = context.discharge_witnesses(conclusion_free, &result);
        if nondominated.iter().any(|d| d.dominates(&result)) {
            continue;
        }
        nondominated.retain(|d| !result.dominates(d));
        nondominated.push(result);
    }
    if !nondominated.is_empty() {
        RuleResult::Established(nondominated)
    } else if !reasons.is_empty() {
        RuleResult::Inconclusive(reasons)
    } else {
        RuleResult::NoMatch
    }
}

/// Provisional typing scopes only. No fact or rule result is accepted until the
/// candidate has been interpreted and matched against the selected source.
pub(super) fn witness_scopes(
    context: &ProofContext,
    candidate: &Expr<()>,
) -> Vec<(DerivationId, BTreeMap<Variable, TypeExpr<()>>)> {
    let accessible = context.types.types.keys().cloned().collect();
    let unbound =
        crate::formula::free_variables_in_context(std::iter::once(candidate), &accessible)
            .difference(&accessible)
            .cloned()
            .collect::<Vec<_>>();
    if unbound.is_empty() {
        return Vec::new();
    }
    fn permutations(values: &[Variable]) -> Vec<Vec<Variable>> {
        if values.is_empty() {
            return vec![Vec::new()];
        }
        let mut result = Vec::new();
        for i in 0..values.len() {
            let mut remaining = values.to_vec();
            let first = remaining.remove(i);
            for mut tail in permutations(&remaining) {
                tail.insert(0, first.clone());
                result.push(tail);
            }
        }
        result
    }
    let mut result = Vec::new();
    for (source, _) in views(context) {
        let analyzed = context
            .analyzed_view(&source)
            .expect("source has checked bindings");
        let Ok(spec) = QuantifierSpec::from_analyzed(&analyzed) else {
            continue;
        };
        if spec.kind != QuantifierKind::Exists || spec.introduced.len() != unbound.len() {
            continue;
        }
        for names in permutations(&unbound) {
            let assignments = spec
                .introduced
                .iter()
                .cloned()
                .zip(names)
                .collect::<BTreeMap<_, _>>();
            let assignments_expr = assignments
                .iter()
                .map(|(v, t)| (v.clone(), Expr::new(RawExpr::Variable(t.clone()))))
                .collect();
            let mut types = BTreeMap::new();
            for binder in &spec.introduced {
                let ty = crate::formula::substitute_free_variables(
                    &Expr::new(RawExpr::Type(spec.bindings[binder].clone())),
                    &assignments_expr,
                );
                let RawExpr::Type(ty) = &ty.raw else {
                    unreachable!()
                };
                types.insert(assignments[binder].clone(), ty.clone());
            }
            result.push((source.derivation, types));
        }
    }
    result
}
