use super::*;

pub(super) fn validate_quantified_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let spec = match analyze_quantifier(sentence, symbolic_types) {
        Ok(spec) => spec,
        Err(message) => {
            validation
                .checks
                .push(StepCheck::QuantifierInconclusive { message });
            return Ok(ClaimResult::default());
        }
    };
    if !spec.questionable.is_empty() {
        validation.checks.push(StepCheck::QuestionableQuantifier {
            premises: spec.questionable.clone(),
        });
    }
    let inherited_facts = proof_facts(proof.tracked, proof.retained);
    if let Some(fact) = inherited_facts
        .iter()
        .find(|fact| *fact == sentence)
        .cloned()
    {
        validation
            .checks
            .push(StepCheck::EstablishedByFact { fact });
        return Ok(ClaimResult {
            assertions: Vec::new(),
            retained: vec![sentence.clone()],
            validated: true,
        });
    }
    match spec.kind {
        QuantifierKind::Exists => {
            match find_existential_witness(&spec, symbolic_types, &inherited_facts) {
                Some(witness) => {
                    validation.checks.push(StepCheck::ExistentialWitness {
                        assignments: witness.assignments.into_iter().collect(),
                        supporting_facts: witness.supporting_facts,
                    });
                    Ok(ClaimResult {
                        assertions: Vec::new(),
                        retained: vec![sentence.clone()],
                        validated: true,
                    })
                }
                None => {
                    validation.checks.push(StepCheck::QuantifierInconclusive {
                        message: "no common syntactic witness was established".to_owned(),
                    });
                    Ok(ClaimResult::default())
                }
            }
        }
        QuantifierKind::Forall => {
            validate_universal_claim(sentence, spec, validation, solver, environment, proof, run)
        }
    }
}

fn validate_universal_claim(
    sentence: &Expr<()>,
    spec: QuantifierSpec,
    validation: &mut StepValidationData,
    solver: &mut Solver,
    environment: Rc<Environment>,
    proof: ProofContext<'_>,
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let ordinary_premises = spec
        .premises
        .iter()
        .filter(|premise| !is_quantifier(premise))
        .cloned()
        .collect::<Vec<_>>();
    let retained_premises = spec
        .premises
        .iter()
        .filter(|premise| is_quantifier(premise))
        .cloned()
        .collect::<Vec<_>>();
    let prepared_premises = ordinary_premises
        .iter()
        .map(|premise| prepare_expression(&spec.types, premise, POSITIVE))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)?;
    let prepared_body = if is_quantifier(&spec.body) {
        None
    } else {
        Some(
            prepare_expression(&spec.types, &spec.body, POSITIVE)
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)?,
        )
    };
    let extensions = quantifier_environment_extensions(
        &environment,
        &spec.types,
        &prepared_premises,
        prepared_body.as_ref(),
        run.max_dimension,
    )?;
    validation.environments_exhaustive &= extensions.exhaustive;
    let mut feasible = 0;
    let mut all_validated = true;
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut local_tracked = proof.tracked.to_vec();
        let mut local_retained = proof.retained.to_vec();
        local_retained.extend(retained_premises.iter().cloned());
        for (premise, prepared) in ordinary_premises.iter().zip(&prepared_premises) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            local_tracked.push((tracker, premise.clone()));
        }
        match solver.check() {
            SatResult::Sat => {
                feasible += 1;
                if is_quantifier(&spec.body) {
                    let facts = proof_facts(&local_tracked, &local_retained);
                    if let Some(fact) = facts.into_iter().find(|fact| fact == &spec.body) {
                        validation
                            .checks
                            .push(StepCheck::EstablishedByFact { fact });
                    } else {
                        validation.checks.push(StepCheck::QuantifierInconclusive {
                            message: "a nested quantified body requires an exact contextual fact"
                                .to_owned(),
                        });
                        all_validated = false;
                    }
                } else {
                    let result = validate_ordinary_claim(
                        &spec.body,
                        validation,
                        solver,
                        Rc::clone(&extension),
                        &spec.types,
                        &local_tracked,
                        run,
                    )?;
                    all_validated &= result.validated;
                }
            }
            SatResult::Unknown => {
                validation.checks.push(StepCheck::Unknown {
                    environment: Some(Rc::clone(&extension)),
                });
                all_validated = false;
            }
            SatResult::Unsat => {}
        }
        solver.pop(1);
        if !all_validated {
            break;
        }
    }
    if feasible == 0 {
        validation.checks.push(StepCheck::VacuousQuantifier);
        return Ok(ClaimResult::default());
    }
    if all_validated {
        Ok(ClaimResult {
            assertions: Vec::new(),
            retained: vec![sentence.clone()],
            validated: true,
        })
    } else {
        Ok(ClaimResult::default())
    }
}

pub(super) enum QuantifierKind {
    Forall,
    Exists,
}

pub(super) struct QuantifierSpec {
    pub(super) kind: QuantifierKind,
    pub(super) premises: Vec<Expr<()>>,
    pub(super) body: Expr<()>,
    pub(super) introduced: BTreeSet<Variable>,
    pub(super) questionable: Vec<Expr<()>>,
    pub(super) types: SymbolicTypeEnvironment,
}

fn quantifier_kind(expression: &Expr<()>) -> Option<QuantifierKind> {
    match expression.raw {
        RawExpr::Finop(Finop::Forall, _) => Some(QuantifierKind::Forall),
        RawExpr::Finop(Finop::Exists, _) => Some(QuantifierKind::Exists),
        _ => None,
    }
}

pub(super) fn analyze_quantifier(
    expression: &Expr<()>,
    active_types: &SymbolicTypeEnvironment,
) -> Result<QuantifierSpec, String> {
    let kind = quantifier_kind(expression)
        .ok_or_else(|| "expression is not a supported quantifier".to_owned())?;
    let RawExpr::Finop(_, expressions) = &expression.raw else {
        unreachable!()
    };
    if expressions.len() < 2 {
        return Err("a quantifier requires at least one premise and a body".to_owned());
    }
    let premises = expressions[..expressions.len() - 1].to_vec();
    let body = expressions.last().unwrap().clone();
    let premise_variables = premises
        .iter()
        .map(|premise| free_variables(std::iter::once(premise)))
        .collect::<Vec<_>>();
    let introduced = premise_variables
        .iter()
        .flatten()
        .filter(|variable| !active_types.types.contains_key(*variable))
        .cloned()
        .collect::<BTreeSet<_>>();
    if introduced.is_empty() {
        return Err(
            "a quantifier must introduce at least one fresh variable in its premises".to_owned(),
        );
    }
    let questionable = premises
        .iter()
        .zip(&premise_variables)
        .filter(|(_, variables)| variables.is_disjoint(&introduced))
        .map(|(premise, _)| premise.clone())
        .collect::<Vec<_>>();

    let inferred = infer_symbolic_type_environment(&premises).map_err(|error| error.to_string())?;
    let mut types = active_types.clone();
    for variable in &introduced {
        let ty = inferred.types.get(variable).cloned().ok_or_else(|| {
            format!(
                "missing inferred type for quantified variable {}",
                variable.z3_name()
            )
        })?;
        types.types.insert(variable.clone(), ty);
    }
    if let Some(variable) = free_variables(std::iter::once(&body))
        .into_iter()
        .find(|variable| !types.types.contains_key(variable))
    {
        return Err(format!(
            "quantifier body contains unbound variable {}",
            variable.z3_name()
        ));
    }
    for child in expressions {
        if is_quantifier(child) {
            analyze_quantifier(child, &types)?;
        } else if contains_quantifier(child) {
            return Err("quantifiers embedded beneath another operator are unsupported".to_owned());
        } else {
            prepare_expression(&types, child, POSITIVE).map_err(|error| error.to_string())?;
        }
    }
    Ok(QuantifierSpec {
        kind,
        premises,
        body,
        introduced,
        questionable,
        types,
    })
}

fn proof_facts(tracked: &[(Bool, Expr<()>)], retained: &[Expr<()>]) -> Vec<Expr<()>> {
    tracked
        .iter()
        .map(|(_, expression)| expression.clone())
        .chain(retained.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct WitnessMatch {
    assignments: BTreeMap<Variable, Expr<()>>,
    supporting_facts: Vec<Expr<()>>,
}

pub(super) fn find_existential_witness(
    spec: &QuantifierSpec,
    active_types: &SymbolicTypeEnvironment,
    facts: &[Expr<()>],
) -> Option<WitnessMatch> {
    let requirements = spec.premises.iter().chain(std::iter::once(&spec.body));
    let accessible = active_types.types.keys().cloned().collect::<BTreeSet<_>>();
    let mut matches = BTreeSet::from([WitnessMatch {
        assignments: BTreeMap::new(),
        supporting_facts: Vec::new(),
    }]);
    for requirement in requirements {
        let mut next = BTreeSet::new();
        for state in &matches {
            for fact in facts {
                let mut unifier = Unifier {
                    metavariables: &spec.introduced,
                    assignments: state.assignments.clone(),
                    pattern_accessible: accessible
                        .iter()
                        .chain(spec.introduced.iter())
                        .cloned()
                        .collect(),
                    candidate_accessible: accessible.clone(),
                    pattern_bound: BTreeSet::new(),
                    candidate_bound: BTreeSet::new(),
                };
                if unifier.expression(requirement, fact) {
                    let mut supporting_facts = state.supporting_facts.clone();
                    if !supporting_facts.contains(fact) {
                        supporting_facts.push(fact.clone());
                    }
                    next.insert(WitnessMatch {
                        assignments: unifier.assignments,
                        supporting_facts,
                    });
                }
            }
        }
        matches = next;
        if matches.is_empty() {
            return None;
        }
    }
    matches.into_iter().find(|candidate| {
        spec.introduced
            .iter()
            .all(|v| candidate.assignments.contains_key(v))
    })
}
