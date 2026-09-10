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
            match find_existential_witness(&spec, symbolic_types, &environment, &inherited_facts) {
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
        .filter(|premise| !is_quantifier(premise) && !spec.is_binder_declaration(premise))
        .cloned()
        .collect::<Vec<_>>();
    let retained_premises = spec
        .premises
        .iter()
        .filter(|premise| is_quantifier(premise))
        .cloned()
        .collect::<Vec<_>>();
    let prepared_premises = prepare_givens(
        &spec.types,
        &ordinary_premises,
        &run.givens,
        run.max_dimension,
    )
    .map_err(ToZ3Error::from)
    .map_err(ModelFindingError::from)?;
    let mut scope = run.givens.clone();
    scope.extend(prepared_premises.iter().cloned());
    let prepared_body = if is_quantifier(&spec.body) {
        None
    } else {
        Some(
            prepare_expression_with_premises(
                &spec.types,
                &spec.body,
                POSITIVE,
                &scope,
                run.max_dimension,
            )
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
                    let scope_len = run.givens.len();
                    run.givens.extend(prepared_premises.iter().cloned());
                    let result = validate_ordinary_claim(
                        &spec.body,
                        validation,
                        solver,
                        Rc::clone(&extension),
                        &spec.types,
                        &local_tracked,
                        run,
                    );
                    run.givens.truncate(scope_len);
                    let result = result?;
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

impl QuantifierSpec {
    fn is_binder_declaration(&self, expression: &Expr<()>) -> bool {
        matches!(
            &expression.raw,
            RawExpr::Variable(variable) if self.introduced.contains(variable)
        )
    }
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
        } else if crate::ellipsis_elimination::contains_ellipses(child) {
            // Analysis establishes scope; interpretation needs the prepared
            // preceding givens available during validation.
            let mut typed = child.with_default_metadata::<crate::type_resolver::TypedMetadata>();
            crate::type_resolver::TypeResolver::new(
                &types,
                &crate::type_resolver::OperatorTypeRules::core(),
            )
            .resolve(&mut typed, POSITIVE)
            .map_err(|error| error.to_string())?;
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
    nonce_pairs: BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
}

pub(super) fn find_existential_witness(
    spec: &QuantifierSpec,
    active_types: &SymbolicTypeEnvironment,
    environment: &Environment,
    facts: &[Expr<()>],
) -> Option<WitnessMatch> {
    let requirements = spec
        .premises
        .iter()
        .filter(|premise| !spec.is_binder_declaration(premise))
        .chain(std::iter::once(&spec.body));
    let accessible = active_types.types.keys().cloned().collect::<BTreeSet<_>>();
    let mut matches = BTreeSet::from([WitnessMatch {
        assignments: BTreeMap::new(),
        supporting_facts: Vec::new(),
        nonce_pairs: BTreeSet::new(),
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
                    bound_forward: BTreeMap::new(),
                    bound_reverse: BTreeMap::new(),
                    nonce_pairs: state.nonce_pairs.clone(),
                };
                if unifier.expression(requirement, fact) {
                    let mut supporting_facts = state.supporting_facts.clone();
                    if !supporting_facts.contains(fact) {
                        supporting_facts.push(fact.clone());
                    }
                    next.insert(WitnessMatch {
                        assignments: unifier.assignments,
                        supporting_facts,
                        nonce_pairs: unifier.nonce_pairs,
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
            && witness_dimensions_match(spec, environment, candidate)
    })
}

fn witness_dimensions_match(
    spec: &QuantifierSpec,
    environment: &Environment,
    witness: &WitnessMatch,
) -> bool {
    let result: Result<bool, ArgumentValidationError> = (|| {
        let prepare = |expression: &Expr<()>| {
            prepare_expression(&spec.types, expression, POSITIVE)
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)
                .map_err(ArgumentValidationError::from)
        };
        let mut assumptions = fixed_assignment_declarations(environment, &spec.types)?;
        assumptions.extend(
            spec.premises
                .iter()
                .map(&prepare)
                .collect::<Result<Vec<_>, _>>()?,
        );
        for (variable, expression) in &witness.assignments {
            let equality = Expr::new(RawExpr::CmpChain(CmpChain {
                start: Expr::new(RawExpr::Variable(variable.clone())),
                assertions: vec![(Cmp::Eq, expression.clone())],
            }));
            assumptions.push(prepare(&equality)?);
        }
        let required = std::iter::once(&spec.body)
            .chain(witness.supporting_facts.iter())
            .map(prepare)
            .collect::<Result<Vec<_>, _>>()?;
        let mut query = crate::enumerable_envspec::dimension_equivalence_query(
            &spec.types,
            &assumptions,
            &required,
        )?;
        Ok(nonce_relationships_match(&mut query, &witness.nonce_pairs))
    })();
    result.unwrap_or(false)
}

fn nonce_relationships_match(
    query: &mut crate::enumerable_envspec::DimensionEquivalenceQuery,
    pairs: &BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
) -> bool {
    let pairs = pairs.iter().copied().collect::<Vec<_>>();
    for (index, (pattern, candidate)) in pairs.iter().enumerate() {
        for (other_pattern, other_candidate) in &pairs[index + 1..] {
            let Some(pattern_equal) = query.necessarily_equal(*pattern, *other_pattern) else {
                return false;
            };
            let Some(candidate_equal) = query.necessarily_equal(*candidate, *other_candidate)
            else {
                return false;
            };
            if pattern_equal != candidate_equal {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Finop, ImplicitDimension, Monop};

    fn dimension(dimension: ImplicitDimension) -> Expr<()> {
        Expr::new(RawExpr::ImplicitDimension(dimension))
    }

    fn equality(left: ImplicitDimension, right: ImplicitDimension) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: dimension(left),
            assertions: vec![(Cmp::Eq, dimension(right))],
        }))
    }

    fn traced_equation(scalar: &str, op: Finop, dimension: ImplicitDimension) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: Expr::new(RawExpr::Finop(
                op,
                vec![
                    Expr::new(RawExpr::Variable(Variable::new(scalar))),
                    Expr::new(RawExpr::Monop(
                        Monop::Trace,
                        Expr::new(RawExpr::IdentityMatrix { dimension }),
                    )),
                ],
            )),
            assertions: vec![(
                Cmp::Eq,
                Expr::new(RawExpr::Variable(Variable::new("result"))),
            )],
        }))
    }

    fn query(
        dimensions: &[ImplicitDimension],
        equalities: &[(ImplicitDimension, ImplicitDimension)],
    ) -> crate::enumerable_envspec::DimensionEquivalenceQuery {
        let types = SymbolicTypeEnvironment::default();
        let mut expressions = dimensions
            .iter()
            .copied()
            .map(dimension)
            .collect::<Vec<_>>();
        expressions.extend(
            equalities
                .iter()
                .map(|(left, right)| equality(*left, *right)),
        );
        let prepared = expressions
            .iter()
            .map(|expression| prepare_expression(&types, expression, POSITIVE).unwrap())
            .collect::<Vec<_>>();
        crate::enumerable_envspec::dimension_equivalence_query(&types, &prepared, &[]).unwrap()
    }

    #[test]
    fn nonce_correspondence_preserves_only_semantically_real_sharing() {
        let pattern = [ImplicitDimension::fresh(), ImplicitDimension::fresh()];
        let candidate = [ImplicitDimension::fresh(), ImplicitDimension::fresh()];
        let dimensions = [pattern[0], pattern[1], candidate[0], candidate[1]];

        let independent_pairs =
            BTreeSet::from([(pattern[0], candidate[0]), (pattern[1], candidate[1])]);
        assert!(nonce_relationships_match(
            &mut query(&dimensions, &[]),
            &independent_pairs,
        ));

        let sharing_mismatch =
            BTreeSet::from([(pattern[0], candidate[0]), (pattern[0], candidate[1])]);
        assert!(!nonce_relationships_match(
            &mut query(&dimensions, &[]),
            &sharing_mismatch,
        ));
        assert!(nonce_relationships_match(
            &mut query(&dimensions, &[(candidate[0], candidate[1])]),
            &sharing_mismatch,
        ));

        let mut incomplete_query = query(&[pattern[0], candidate[0]], &[]);
        assert!(!nonce_relationships_match(
            &mut incomplete_query,
            &independent_pairs,
        ));
    }

    #[test]
    fn existential_matching_carries_nonce_correspondence_across_requirements() {
        let x = Variable::new("x");
        let a = Variable::new("a");
        let result = Variable::new("result");
        let pattern_dimension = ImplicitDimension::fresh();
        let spec = QuantifierSpec {
            kind: QuantifierKind::Exists,
            premises: vec![traced_equation("x", Finop::Plus, pattern_dimension)],
            body: traced_equation("x", Finop::Times, pattern_dimension),
            introduced: BTreeSet::from([x.clone()]),
            questionable: Vec::new(),
            types: SymbolicTypeEnvironment {
                types: [
                    (x, TypeExpr::Real),
                    (a.clone(), TypeExpr::Real),
                    (result.clone(), TypeExpr::Real),
                ]
                .into_iter()
                .collect(),
            },
        };
        let active = SymbolicTypeEnvironment {
            types: [(a, TypeExpr::Real), (result, TypeExpr::Real)]
                .into_iter()
                .collect(),
        };
        let independent_facts = vec![
            traced_equation("a", Finop::Plus, ImplicitDimension::fresh()),
            traced_equation("a", Finop::Times, ImplicitDimension::fresh()),
        ];
        assert!(
            find_existential_witness(&spec, &active, &Environment::default(), &independent_facts,)
                .is_none()
        );

        let shared_dimension = ImplicitDimension::fresh();
        let shared_facts = vec![
            traced_equation("a", Finop::Plus, shared_dimension),
            traced_equation("a", Finop::Times, shared_dimension),
        ];
        assert!(
            find_existential_witness(&spec, &active, &Environment::default(), &shared_facts,)
                .is_some()
        );
    }
}
