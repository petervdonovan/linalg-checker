use super::*;

pub(super) struct InductionObligations {
    pub(super) base: Expr<()>,
    pub(super) step: Expr<()>,
}

impl InductionObligations {
    pub(super) fn new(goal: &Goal, variable: &Variable, start: u64) -> Self {
        let base_value = Expr::new(RawExpr::NatLiteral(start));
        let variable_expression = Expr::new(RawExpr::Variable(variable.clone()));
        let successor = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                variable_expression.clone(),
                Expr::new(RawExpr::NatLiteral(1)),
            ],
        ));
        let base_givens = goal
            .givens
            .iter()
            .map(|given| substitute_free_variable(given, variable, &base_value))
            .collect::<Vec<_>>();
        let base_conclusion = substitute_free_variable(&goal.conclusion, variable, &base_value);
        let hypothesis = scoped_goal_expression(&goal.givens, &goal.conclusion);
        let mut step_givens = vec![hypothesis];
        step_givens.extend(
            goal.givens
                .iter()
                .map(|given| substitute_free_variable(given, variable, &successor)),
        );
        let step_conclusion = substitute_free_variable(&goal.conclusion, variable, &successor);
        Self {
            base: scoped_goal_expression(&base_givens, &base_conclusion),
            step: scoped_goal_expression(&step_givens, &step_conclusion),
        }
    }

    pub(super) fn matches_base(&self, goal: &Goal) -> bool {
        scoped_goal_expression(&goal.givens, &goal.conclusion) == self.base
    }

    pub(super) fn matches_step(&self, goal: &Goal) -> bool {
        scoped_goal_expression(&goal.givens, &goal.conclusion) == self.step
    }
}

pub(super) fn natural_lower_bound(variable: &Variable, start: u64) -> Expr<()> {
    Expr::new(RawExpr::CmpChain(CmpChain {
        start: Expr::new(RawExpr::Variable(variable.clone())),
        assertions: vec![(Cmp::Ge, Expr::new(RawExpr::NatLiteral(start)))],
    }))
}

pub(super) fn infer_induction_start(
    goal: &Goal,
    variable: &Variable,
    base: &Environment,
    parent_types: &SymbolicTypeEnvironment,
    enclosing: &[PreparedExpression],
    max_dimension: u64,
) -> Result<Option<u64>, ArgumentValidationError> {
    for value in 0..=max_dimension {
        let replacement = Expr::new(RawExpr::NatLiteral(value));
        let givens = goal
            .givens
            .iter()
            .filter(|given| !is_quantifier(given))
            .map(|given| substitute_free_variable(given, variable, &replacement))
            .collect::<Vec<_>>();
        let conclusion = substitute_free_variable(&goal.conclusion, variable, &replacement);
        let (types, _) = match extend_symbolic_types(parent_types, &givens) {
            Ok(types) => types,
            Err(ArgumentValidationError::Shape(ShapeError::InvalidTyping(_))) => continue,
            Err(error) => return Err(error),
        };
        let prepared_givens = match prepare_givens(&types, &givens, enclosing, max_dimension) {
            Ok(prepared) => prepared,
            Err(TypeError::Invalid(_)) => continue,
            Err(error) => return Err(ModelFindingError::from(ToZ3Error::from(error)).into()),
        };
        let mut scope = enclosing.to_vec();
        scope.extend(prepared_givens.iter().cloned());
        let prepared_conclusion = match prepare_expression_with_premises(
            &types,
            &conclusion,
            POSITIVE,
            &scope,
            max_dimension,
        ) {
            Ok(prepared) => prepared,
            Err(TypeError::Invalid(_)) => continue,
            Err(error) => return Err(ModelFindingError::from(ToZ3Error::from(error)).into()),
        };
        let mut assumptions = fixed_assignment_declarations(base, &types)?;
        assumptions.extend(prepared_givens);
        let iterator = match extract_prepared_environment_iterator_with_required_context(
            &types,
            &assumptions,
            std::slice::from_ref(&prepared_conclusion),
            &[],
            max_dimension,
        ) {
            Ok(iterator) => iterator,
            Err(ShapeError::Unsat(_) | ShapeError::InvalidTyping(_)) => continue,
            Err(error) => return Err(error.into()),
        };
        if iterator.into_iter().next().transpose()?.is_some() {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

pub(super) fn validate_tactic_fallback(
    goal: &mut Goal,
    solver: &mut Solver,
    base: Rc<Environment>,
    parent_types: &SymbolicTypeEnvironment,
    tracked: &[TrackedFact],
    scoped_statements: &[Expr<()>],
    run: &mut ValidationRun,
) -> Result<ClaimResult, ArgumentValidationError> {
    let ordinary_givens = goal
        .givens
        .iter()
        .filter(|given| !is_quantifier(given))
        .cloned()
        .collect::<Vec<_>>();
    let (mut types, _) = extend_symbolic_types(parent_types, &ordinary_givens)?;
    let Tactic::Induction { variable } = goal.tactic.as_ref().unwrap();
    types.types.insert(variable.clone(), TypeExpr::Nat);
    let prepared_givens = prepare_givens(&types, &ordinary_givens, &run.givens, run.max_dimension)
        .map_err(ToZ3Error::from)
        .map_err(ModelFindingError::from)?;
    let extensions =
        goal_environment_extensions(&base, &types, &prepared_givens, &[], run.max_dimension)?;
    goal.validation.environments_exhaustive &= extensions.exhaustive;
    if extensions.environments.is_empty() {
        goal.validation
            .checks
            .push(StepCheck::DimensionallyInvalid {
                environment: base,
                declarations: Vec::new(),
            });
        return Ok(ClaimResult::default());
    }

    let mut all_validated = true;
    for extension in extensions.environments {
        let extension = Rc::new(extension);
        solver.push();
        assert_natural_assignment(solver, &extension);
        let mut local_tracked = tracked.to_vec();
        for (given, prepared) in ordinary_givens.iter().zip(&prepared_givens) {
            let assertion = lower_prepared_boolean(&extension, prepared)?;
            assert_definitions(solver, &assertion.side_conditions)?;
            let tracker = fresh_tracker(&mut run.next_tracker);
            solver.assert_and_track(assertion.expression, &tracker);
            local_tracked.push(TrackedFact {
                tracker,
                sentence: given.clone(),
                alternatives: prepared.expression.meta.alternatives().to_vec(),
            });
        }
        if matches!(solver.check(), SatResult::Sat) {
            let scope_len = run.givens.len();
            run.givens.extend(prepared_givens.iter().cloned());
            let result = validate_claim(
                &goal.conclusion,
                &mut goal.validation,
                solver,
                Rc::clone(&extension),
                &types,
                ProofContext {
                    tracked: &local_tracked,
                    retained: scoped_statements,
                },
                run,
                false,
            );
            run.givens.truncate(scope_len);
            let result = result?;
            all_validated &= result.validated;
        }
        solver.pop(1);
    }
    Ok(ClaimResult {
        assertions: Vec::new(),
        retained: Vec::new(),
        introduced_types: BTreeMap::new(),
        alternatives: Vec::new(),
        validated: all_validated,
    })
}
