//! Symbolic, statement-ordered validation. Concrete solvers are local to fallback
//! checks; only the aggregate result can add a formula to the shared context.
use super::*;
use crate::natural_deduction as nd;
use crate::type_resolver::{MaybeTyped, analyze_formula};

#[derive(Default)]
pub(super) struct GoalOutcome {
    pub validated: bool,
    pub exported: bool,
}

fn error_check(validation: &mut StepValidationData, error: ModelFindingError) {
    validation.checks.push(StepCheck::Error {
        environment: Rc::new(Environment::default()),
        error,
    });
}
fn prepared_facts(
    context: &nd::ProofContext,
    run: &ValidationRun,
) -> Result<Vec<(Expr<()>, PreparedExpression)>, ModelFindingError> {
    let mut facts = Vec::new();
    for fact in context.facts() {
        if let Some(prepared) = run.interpretations.get(&fact.id) {
            facts.push((fact.expression.clone(), prepared.clone()));
            continue;
        }
        let expression = fact
            .analyzed
            .as_ref()
            .map(|e| {
                crate::type_resolver::avoid_bound_collisions(
                    e,
                    &context.types.types.keys().cloned().collect(),
                )
                .with_default_metadata()
            })
            .unwrap_or_else(|| fact.expression.clone());
        match prepare_expression_with_premises(
            &context.types,
            &expression,
            POSITIVE,
            &run.givens,
            run.max_dimension,
            &run.timings,
        ) {
            Ok(prepared) => facts.push((fact.expression.clone(), prepared)),
            Err(TypeError::Unsupported(_)) if contains_quantifier(&expression) => {}
            Err(error) => return Err(ModelFindingError::from_type(error)),
        }
    }
    Ok(facts)
}

fn solver_for(
    environment: &Environment,
    facts: &[(Expr<()>, PreparedExpression)],
    run: &mut ValidationRun,
) -> Result<(Solver, Vec<TrackedFact>), ModelFindingError> {
    let mut solver = crate::z3_utils::value_solver();
    assert_natural_assignment(&solver, environment);
    let mut tracked = Vec::new();
    for (sentence, prepared) in facts {
        let assertion = lower_prepared_boolean(environment, prepared)?;
        track_assertions(
            &mut solver,
            &[assertion],
            sentence.clone(),
            &mut tracked,
            &mut run.next_tracker,
        )?;
    }
    Ok((solver, tracked))
}
fn feasible(
    context: &nd::ProofContext,
    run: &mut ValidationRun,
) -> Result<(bool, bool), ArgumentValidationError> {
    let extensions = goal_environment_extensions(
        &Environment::default(),
        &context.types,
        &run.givens,
        &[],
        run.max_dimension,
        &run.timings,
    )?;
    let facts = run
        .lexical_expressions
        .iter()
        .cloned()
        .zip(run.givens.iter().cloned())
        .collect::<Vec<_>>();
    for environment in extensions.environments {
        let (solver, _) = solver_for(&environment, &facts, run)?;
        match run.timings.check(&solver, "z3_real_ms") {
            SatResult::Sat => return Ok((true, extensions.exhaustive)),
            SatResult::Unknown => return Ok((true, false)),
            SatResult::Unsat => {}
        }
    }
    Ok((false, extensions.exhaustive))
}

fn initialize_scope(
    goal: &mut Goal,
    context: &mut nd::ProofContext,
    run: &mut ValidationRun,
    forced: Option<(&Variable, u64)>,
) -> Result<(BTreeSet<Variable>, BTreeSet<nd::AssumptionId>), String> {
    context.enter_scope();
    let mut introduced = BTreeSet::new();
    let mut assumptions = BTreeSet::new();
    if let Some((variable, _)) = forced {
        if context.types.types.contains_key(variable) {
            return Err(format!(
                "induction-step binder {} collides with its enclosing scope",
                variable.z3_name()
            ));
        }
        context.declare_parameter(variable.clone(), TypeExpr::Nat);
        introduced.insert(variable.clone());
    }
    for given in &goal.givens {
        if !contains_quantifier(given) {
            let (types, new) = extend_symbolic_types(&context.types, std::slice::from_ref(given))
                .map_err(|e| e.to_string())?;
            for variable in &new {
                context.declare_parameter(variable.clone(), types.types[variable].clone());
            }
            introduced.extend(new);
        }
        let typed = analyze_formula(&context.types, given).map_err(|e| e.to_string())?;
        if let Ok(spec) = QuantifierSpec::from_analyzed(&typed)
            && !spec.questionable.is_empty()
        {
            goal.validation
                .checks
                .push(StepCheck::QuestionableQuantifier {
                    premises: spec.questionable,
                });
        }
        let prepared = match prepare_expression_with_premises(
            &context.types,
            given,
            POSITIVE,
            &run.givens,
            run.max_dimension,
            &run.timings,
        ) {
            Ok(prepared) => Some(prepared),
            Err(TypeError::Unsupported(_)) if contains_quantifier(given) => None,
            Err(error) => return Err(error.to_string()),
        };
        let alternatives = prepared
            .as_ref()
            .map(|p| p.expression.meta.alternatives().to_vec())
            .unwrap_or_default();
        assumptions.insert(context.assume(given.clone(), alternatives));
        if let Some(prepared) = prepared {
            let fact = context
                .facts()
                .iter()
                .find(|f| f.expression == *given)
                .unwrap();
            run.interpretations.insert(fact.id, prepared.clone());
            run.lexical_expressions.push(given.clone());
            run.givens.push(prepared);
        }
    }
    if let Some((variable, start)) = forced {
        let bound = natural_lower_bound(variable, start);
        let prepared = prepare_expression_with_premises(
            &context.types,
            &bound,
            POSITIVE,
            &run.givens,
            run.max_dimension,
            &run.timings,
        )
        .map_err(|e| e.to_string())?;
        run.lexical_expressions.push(bound.clone());
        run.givens.push(prepared);
        assumptions.insert(context.assume(bound, Vec::new()));
    }
    Ok((introduced, assumptions))
}

pub(super) fn validate_goal(
    goal: &mut Goal,
    parent: &mut nd::ProofContext,
    run: &mut ValidationRun,
    forced: Option<(&Variable, u64)>,
) -> Result<GoalOutcome, ArgumentValidationError> {
    if goal.tactic.is_some() {
        return validate_induction(goal, parent, run);
    }
    let scope_len = run.givens.len();
    let mut context = parent.clone();
    let initialized = initialize_scope(goal, &mut context, run, forced);
    let result = (|| {
        let (introduced, assumptions) = match initialized {
            Ok(value) => value,
            Err(message) => {
                goal.validation
                    .checks
                    .push(StepCheck::QuantifierInconclusive { message });
                return Ok(GoalOutcome::default());
            }
        };
        let (possible, exhaustive) = feasible(&context, run)?;
        if !possible {
            record_inconsistent_givens(goal, exhaustive, run.max_dimension);
            return Ok(GoalOutcome::default());
        }
        goal.validation.givens_feasible = true;
        for item in &mut goal.steps {
            match item {
                ArgumentItem::Sentence(step) => {
                    validate_claim(&step.sentence, &mut step.validation, &mut context, run)?;
                }
                ArgumentItem::Goal(child) => {
                    validate_goal(child, &mut context, run, None)?;
                }
            }
        }
        let validated = validate_claim(&goal.conclusion, &mut goal.validation, &mut context, run)?;
        // Export independent internal facts even when the requested conclusion failed.
        let facts = context.exportable_to(parent);
        for fact in facts {
            parent.import(fact, &context.archive);
        }
        let exported = validated
            && export_goal(
                goal,
                &context,
                parent,
                &introduced,
                &assumptions,
                run,
                scope_len,
            );
        Ok(GoalOutcome {
            validated,
            exported,
        })
    })();
    run.givens.truncate(scope_len);
    run.lexical_expressions.truncate(scope_len);
    result
}

fn export_goal(
    goal: &Goal,
    context: &nd::ProofContext,
    parent: &mut nd::ProofContext,
    introduced: &BTreeSet<Variable>,
    discharged: &BTreeSet<nd::AssumptionId>,
    run: &mut ValidationRun,
    scope_len: usize,
) -> bool {
    let mut givens = goal
        .givens
        .iter()
        .map(|given| {
            context
                .facts()
                .iter()
                .find(|f| f.expression == *given)
                .and_then(|f| f.analyzed.as_ref())
                .map(|e| {
                    crate::type_resolver::avoid_bound_collisions(
                        e,
                        &context.types.types.keys().cloned().collect(),
                    )
                    .with_default_metadata()
                })
                .unwrap_or_else(|| given.clone())
        })
        .collect::<Vec<Expr<()>>>();
    for id in discharged {
        if let Some(a) = context.assumptions().get(id)
            && !goal.givens.contains(&a.expression)
        {
            givens.push(a.expression.clone());
        }
    }
    let statement = exported_goal_expression(introduced, &givens, &goal.conclusion);
    // Export eligibility is distinct from validity of the goal inside its scope.
    if analyze_formula(&parent.types, &statement).is_err() {
        return false;
    }
    let Some(fact) = context
        .facts()
        .iter()
        .find(|f| f.expression == goal.conclusion)
    else {
        return false;
    };
    let mut proofs = Vec::new();
    for source in &fact.derivations {
        let mut d = source.clone();
        d.assumptions.retain(|a| !discharged.contains(a));
        d.required_variables.retain(|v| !introduced.contains(v));
        if !d
            .assumptions
            .iter()
            .all(|a| parent.assumptions().contains_key(a))
            || !d
                .required_variables
                .iter()
                .all(|v| parent.types.types.contains_key(v))
        {
            continue;
        }
        d.proof = nd::NaturalDeductionProof::ScopedGoal {
            givens: goal.givens.clone(),
            conclusion: goal.conclusion.clone(),
            cases: vec![source.id],
        };
        parent.refresh_scopes(&mut d, &statement);
        proofs.push(d);
    }
    if proofs.is_empty() {
        return false;
    }
    parent.archive.extend(context.archive.clone());
    parent.record(statement.clone(), Vec::new(), proofs);
    if !contains_quantifier(&statement)
        && let Some(prepared) = run.interpretations.get(&fact.id).cloned()
        && let Some(exported) = parent.facts().iter().find(|f| f.expression == statement)
    {
        run.interpretations
            .insert(exported.id, prepared.under_givens(&run.givens[scope_len..]));
    }
    true
}

fn validate_induction(
    goal: &mut Goal,
    parent: &mut nd::ProofContext,
    run: &mut ValidationRun,
) -> Result<GoalOutcome, ArgumentValidationError> {
    let Tactic::Induction { variable } = goal.tactic.as_ref().unwrap();
    let variable = variable.clone();
    if parent.types.types.contains_key(&variable)
        || !free_variables(goal.givens.iter().chain(std::iter::once(&goal.conclusion)))
            .contains(&variable)
    {
        goal.validation.checks.push(StepCheck::InvalidTactic {
            message: format!(
                "the induction variable {} must be fresh and occur in the goal",
                variable.z3_name()
            ),
        });
        return Ok(GoalOutcome::default());
    }
    let Some(start) = infer_induction_start(
        goal,
        &variable,
        &Environment::default(),
        &parent.types,
        &run.givens,
        run.max_dimension,
        &run.timings,
    )?
    else {
        goal.validation.checks.push(StepCheck::InvalidTactic {
            message: format!(
                "no admissible starting value for {} was found up to {}",
                variable.z3_name(),
                run.max_dimension
            ),
        });
        return Ok(GoalOutcome::default());
    };
    // The induction goal's givens are a schema, not assumptions from which to
    // prove that same schema. Base/step scopes instantiate and type it themselves.
    let obligations = InductionObligations::new(goal, &variable, start);
    let mut context = parent.clone();
    let mut base = false;
    let mut step = false;
    for item in &mut goal.steps {
        match item {
            ArgumentItem::Sentence(sentence) => {
                validate_claim(
                    &sentence.sentence,
                    &mut sentence.validation,
                    &mut context,
                    run,
                )?;
            }
            ArgumentItem::Goal(child) => {
                let is_base = obligations.matches_base(child);
                let is_step = obligations.matches_step(child);
                let outcome = validate_goal(
                    child,
                    &mut context,
                    run,
                    is_step.then_some((&variable, start)),
                )?;
                base |= is_base && outcome.validated && outcome.exported;
                step |= is_step && outcome.validated && outcome.exported;
            }
        }
    }
    if base && step {
        goal.validation.environments_exhaustive = true;
        goal.validation.givens_feasible = true;
        goal.validation.checks.push(StepCheck::TacticEstablished);
        let statement = scoped_goal_expression(&goal.givens, &goal.conclusion);
        context.record_external_with_proof(
            statement.clone(),
            Vec::new(),
            nd::NaturalDeductionProof::ScopedGoal {
                givens: goal.givens.clone(),
                conclusion: goal.conclusion.clone(),
                cases: Vec::new(),
            },
        );
        for fact in context.exportable_to(parent) {
            parent.import(fact, &context.archive);
        }
        return Ok(GoalOutcome {
            validated: true,
            exported: parent.facts().iter().any(|f| f.expression == statement),
        });
    }
    goal.validation.checks.push(StepCheck::IncompleteSubgoals {
        expected: [
            (!base).then_some(obligations.base),
            (!step).then_some(obligations.step),
        ]
        .into_iter()
        .flatten()
        .collect(),
    });
    let scope_len = run.givens.len();
    let mut schema = context.clone();
    let initialized = initialize_scope(goal, &mut schema, run, Some((&variable, start)));
    let result = match initialized {
        Ok((introduced, assumptions)) => {
            let validated =
                validate_claim(&goal.conclusion, &mut goal.validation, &mut schema, run)?;
            let exported = validated
                && export_goal(
                    goal,
                    &schema,
                    parent,
                    &introduced,
                    &assumptions,
                    run,
                    scope_len,
                );
            GoalOutcome {
                validated,
                exported,
            }
        }
        Err(message) => {
            goal.validation
                .checks
                .push(StepCheck::QuantifierInconclusive { message });
            GoalOutcome::default()
        }
    };
    run.givens.truncate(scope_len);
    run.lexical_expressions.truncate(scope_len);
    Ok(result)
}

fn proof_check(proof: &nd::NaturalDeductionProof) -> StepCheck {
    use nd::NaturalDeductionProof::*;
    let premises: Vec<&nd::Premise> = match proof {
        Reuse { premise }
        | UniversalIntroduction { premise, .. }
        | ImplicationIntroduction { premise, .. } => vec![premise],
        ExistentialIntroduction { premises, .. } => premises.iter().collect(),
        ExistentialElimination { source, .. } => vec![source],
        UniversalElimination {
            source, premises, ..
        } => std::iter::once(source).chain(premises).collect(),
        _ => Vec::new(),
    };
    let mut supporting_facts = Vec::new();
    for p in premises {
        if !supporting_facts.contains(&p.expression) {
            supporting_facts.push(p.expression.clone());
        }
    }
    match proof {
        ExistentialIntroduction { assignments, .. } => StepCheck::ExistentialWitness {
            assignments: assignments
                .iter()
                .map(|(v, e)| (v.clone(), e.clone()))
                .collect(),
            supporting_facts,
        },
        ExistentialElimination {
            source,
            assignments,
            ..
        } => StepCheck::ExistentialElimination {
            fact: source.expression.clone(),
            assignments: assignments
                .iter()
                .map(|(a, b)| (a.clone(), b.clone()))
                .collect(),
        },
        _ => StepCheck::NaturalDeduction {
            proof: proof.clone(),
            supporting_facts,
        },
    }
}

fn check_definedness(
    prepared: &PreparedExpression,
    context: &nd::ProofContext,
    validation: &mut StepValidationData,
    run: &mut ValidationRun,
) -> Result<bool, ArgumentValidationError> {
    if prepared
        .side_conditions
        .iter()
        .all(|c| matches!(c.existence, crate::visit_mut::Existence::Guaranteed))
    {
        return Ok(true);
    }
    let facts = prepared_facts(context, run)?;
    let extensions = goal_environment_extensions(
        &Environment::default(),
        &context.types,
        &run.givens,
        std::slice::from_ref(prepared),
        run.max_dimension,
        &run.timings,
    )?;
    if !extensions.exhaustive {
        validation
            .checks
            .push(StepCheck::Unknown { environment: None });
        return Ok(false);
    }
    if extensions.environments.is_empty() {
        validation.checks.push(StepCheck::DimensionallyInvalid {
            environment: Rc::new(Environment::default()),
            declarations: Vec::new(),
        });
        return Ok(false);
    }
    for environment in extensions.environments {
        let environment = Rc::new(environment);
        let (mut solver, _) = solver_for(&environment, &facts, run)?;
        let lowered = lower_prepared_boolean(&environment, prepared)?;
        let warnings = check_step_existence(
            &mut solver,
            environment,
            &context.types,
            &lowered.side_conditions,
            &run.timings,
        )?;
        if !warnings.is_empty() {
            validation.checks.extend(warnings);
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn validate_claim(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    context: &mut nd::ProofContext,
    run: &mut ValidationRun,
) -> Result<bool, ArgumentValidationError> {
    let mut candidates = vec![sentence.clone()];
    let mut alternatives = Vec::new();
    let mut interpretation = None;
    let analysis = analyze_formula(&context.types, sentence);
    if analysis.is_ok()
        && !contains_quantifier(sentence)
        && let Ok(prepared) = prepare_expression_with_premises(
            &context.types,
            sentence,
            POSITIVE,
            &run.givens,
            run.max_dimension,
            &run.timings,
        )
    {
        alternatives = prepared.expression.meta.alternatives().to_vec();
        interpretation = Some(prepared);
        candidates.extend(alternatives.iter().filter(|e| is_quantifier(e)).cloned());
    }
    let mut checks = quantifier::DimensionChecks {
        evidence: Vec::new(),
        context,
        givens: &run.givens,
        timings: &run.timings,
    };
    let mut proposals = None;
    for candidate in &candidates {
        if let nd::NaturalDeductionResult::Established { derivations } =
            nd::follows_from_natural_deduction(context, candidate, &mut checks)
        {
            proposals = Some(derivations);
            break;
        }
    }
    if let Some(mut derivations) = proposals {
        // Selecting a source is explicit and commits exactly one witness choice.
        let selected = derivations.iter().position(|d| {
            matches!(
                d.proof,
                nd::NaturalDeductionProof::ExistentialElimination { .. }
            )
        });
        let mut checking_scope = std::borrow::Cow::Borrowed(&*context);
        if let Some(index) = selected {
            let chosen = derivations.remove(index);
            if let nd::NaturalDeductionProof::ExistentialElimination {
                introduced_types, ..
            } = &chosen.proof
            {
                let scope = checking_scope.to_mut();
                scope.enter_scope();
                for (v, ty) in introduced_types {
                    scope.declare_parameter(v.clone(), ty.clone());
                }
            }
            derivations = vec![chosen];
        }
        if let Err(error) = analyze_formula(&checking_scope.types, sentence) {
            error_check(validation, ModelFindingError::from_type(error));
            return Ok(false);
        }
        // Logical justification is already complete. Preprocessing is only for
        // well-definedness and elaborated views, never for finite proof checking.
        if !contains_quantifier(sentence) {
            match prepare_expression_with_premises(
                &checking_scope.types,
                sentence,
                POSITIVE,
                &run.givens,
                run.max_dimension,
                &run.timings,
            ) {
                Ok(prepared) => {
                    alternatives = prepared.expression.meta.alternatives().to_vec();
                    interpretation = Some(prepared);
                }
                Err(error) => {
                    error_check(validation, ModelFindingError::from_type(error));
                    return Ok(false);
                }
            }
        }
        // Fresh terms in universal instantiation need their own domain checks,
        // including when the resulting formula still contains quantifiers.
        if let nd::NaturalDeductionProof::UniversalElimination { assignments, .. } =
            &derivations[0].proof
        {
            for term in assignments.values() {
                let reflexivity = Expr::new(RawExpr::CmpChain(CmpChain {
                    start: term.clone(),
                    assertions: vec![(Cmp::Eq, term.clone())],
                }));
                let prepared = prepare_expression_with_premises(
                    &checking_scope.types,
                    &reflexivity,
                    POSITIVE,
                    &run.givens,
                    run.max_dimension,
                    &run.timings,
                )
                .map_err(ModelFindingError::from_type)?;
                if !check_definedness(&prepared, &checking_scope, validation, run)? {
                    return Ok(false);
                }
            }
        }
        if selected.is_none()
            && let Some(prepared) = &interpretation
            && !check_definedness(prepared, &checking_scope, validation, run)?
        {
            return Ok(false);
        }
        validation.environments_exhaustive = true;
        validation.checks.push(proof_check(&derivations[0].proof));
        if let Ok(spec) = analyze_quantifier(sentence, &context.types)
            && !spec.questionable.is_empty()
        {
            validation.checks.push(StepCheck::QuestionableQuantifier {
                premises: spec.questionable,
            });
        }
        if selected.is_some() {
            context.open_witness(sentence.clone(), alternatives, derivations.remove(0));
        } else {
            context.record(sentence.clone(), alternatives, derivations);
        }
        if let Some(prepared) = interpretation
            && let Some(fact) = context.facts().iter().find(|f| f.expression == *sentence)
        {
            run.interpretations.insert(fact.id, prepared);
        }
        return Ok(true);
    }
    if let Err(error) = analysis {
        if contains_quantifier(sentence) {
            validation.checks.push(StepCheck::QuantifierInconclusive {
                message: error.to_string(),
            });
        } else {
            error_check(validation, ModelFindingError::from_type(error));
        }
        return Ok(false);
    }
    let accepted = if let Ok(spec) = analyze_quantifier(sentence, &context.types) {
        if !spec.questionable.is_empty() {
            validation.checks.push(StepCheck::QuestionableQuantifier {
                premises: spec.questionable.clone(),
            });
        }
        match spec.kind {
            QuantifierKind::Exists => {
                validation.checks.push(StepCheck::QuantifierInconclusive {
                    message: "no common syntactic witness was established".into(),
                });
                false
            }
            QuantifierKind::Forall => bounded_universal(&spec, validation, context, run)?,
        }
    } else if contains_quantifier(sentence) {
        validation.checks.push(StepCheck::QuantifierInconclusive {
            message: "verification failed to handle the quantifiers in this formula".into(),
        });
        false
    } else {
        bounded_ordinary(sentence, validation, context, run)?
    };
    if accepted
        && let Some(prepared) = &interpretation
        && !check_definedness(prepared, context, validation, run)?
    {
        return Ok(false);
    }
    if accepted {
        context.record_external(sentence.clone(), alternatives);
        if let Some(prepared) = interpretation
            && let Some(fact) = context.facts().iter().find(|f| f.expression == *sentence)
        {
            run.interpretations.insert(fact.id, prepared);
        }
    }
    Ok(accepted)
}

fn bounded_ordinary(
    sentence: &Expr<()>,
    validation: &mut StepValidationData,
    context: &nd::ProofContext,
    run: &mut ValidationRun,
) -> Result<bool, ArgumentValidationError> {
    let facts = match prepared_facts(context, run) {
        Ok(f) => f,
        Err(e) => {
            error_check(validation, e);
            return Ok(false);
        }
    };
    let prepared_context = facts.iter().map(|(_, p)| p.clone()).collect::<Vec<_>>();
    let extensions = goal_environment_extensions(
        &Environment::default(),
        &context.types,
        &run.givens,
        &prepared_context,
        run.max_dimension,
        &run.timings,
    )?;
    validation.environments_exhaustive = extensions.exhaustive;
    if extensions.environments.is_empty() {
        validation.checks.push(StepCheck::DimensionallyInvalid {
            environment: Rc::new(Environment::default()),
            declarations: Vec::new(),
        });
        return Ok(false);
    }
    let mut accepted = true;
    for environment in extensions.environments {
        let environment = Rc::new(environment);
        let (mut solver, tracked) = solver_for(&environment, &facts, run)?;
        let result = validate_ordinary_claim(
            sentence,
            validation,
            &mut solver,
            environment,
            &context.types,
            &tracked,
            run,
            false,
        )?;
        accepted &= result.validated;
        if !accepted {
            break;
        }
    }
    accepted &= !validation.checks.iter().any(|c| {
        matches!(
            c,
            StepCheck::Unknown { .. }
                | StepCheck::MayBeUndefined { .. }
                | StepCheck::AssumedExistence { .. }
                | StepCheck::Error { .. }
        )
    });
    Ok(accepted)
}

fn bounded_universal(
    spec: &QuantifierSpec,
    validation: &mut StepValidationData,
    context: &nd::ProofContext,
    run: &mut ValidationRun,
) -> Result<bool, ArgumentValidationError> {
    let len = run.givens.len();
    let mut local = context.clone();
    local.enter_scope();
    for (v, t) in &spec.bindings {
        local.declare_parameter(v.clone(), t.clone());
    }
    let result = (|| {
        for premise in &spec.premises {
            if !contains_quantifier(premise) && !spec.is_binder_declaration(premise) {
                let prepared = prepare_expression_with_premises(
                    &local.types,
                    premise,
                    POSITIVE,
                    &run.givens,
                    run.max_dimension,
                    &run.timings,
                )
                .map_err(ModelFindingError::from_type)?;
                run.givens.push(prepared);
                run.lexical_expressions.push(premise.clone());
            }
            if !spec.is_binder_declaration(premise) {
                local.assume(premise.clone(), Vec::new());
            }
        }
        let (possible, _) = feasible(&local, run)?;
        if !possible {
            validation.checks.push(StepCheck::VacuousQuantifier);
            return Ok(false);
        }
        validate_claim(&spec.body, validation, &mut local, run)
    })();
    run.givens.truncate(len);
    run.lexical_expressions.truncate(len);
    result
}
