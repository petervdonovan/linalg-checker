use super::*;
use crate::timing::Timings;

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
    timings: &Timings,
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
        let prepared_givens =
            match prepare_givens(&types, &givens, enclosing, max_dimension, timings) {
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
            timings,
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
            timings,
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
