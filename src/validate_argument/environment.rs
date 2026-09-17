use super::*;

pub(super) fn extend_symbolic_types(
    parent: &SymbolicTypeEnvironment,
    givens: &[Expr<()>],
) -> Result<(SymbolicTypeEnvironment, BTreeSet<Variable>), ArgumentValidationError> {
    let variables = free_variables(givens.iter());
    let introduced = variables
        .iter()
        .filter(|variable| !parent.types.contains_key(*variable))
        .cloned()
        .collect::<BTreeSet<_>>();
    let inferred = infer_symbolic_type_environment(givens)?;
    let mut extended = parent.clone();
    for variable in &introduced {
        let ty = inferred.types.get(variable).cloned().ok_or_else(|| {
            ShapeError::InvalidTyping(format!(
                "missing inferred type for introduced variable {}",
                variable.z3_name()
            ))
        })?;
        extended.types.insert(variable.clone(), ty);
    }
    Ok((extended, introduced))
}

pub(super) struct AnalyzedGivens {
    pub(super) ordinary: Vec<Expr<()>>,
    pub(super) retained: Vec<Expr<()>>,
    pub(super) symbolic_types: SymbolicTypeEnvironment,
    pub(super) introduced: BTreeSet<Variable>,
    pub(super) questionable: Vec<Expr<()>>,
}

pub(super) fn analyze_goal_givens(
    parent: &SymbolicTypeEnvironment,
    givens: &[Expr<()>],
    forced_natural: Option<&Variable>,
) -> Result<AnalyzedGivens, String> {
    let mut result = AnalyzedGivens {
        ordinary: Vec::new(),
        retained: Vec::new(),
        symbolic_types: parent.clone(),
        introduced: BTreeSet::new(),
        questionable: Vec::new(),
    };
    let mut forced_inserted = false;
    for given in givens {
        if is_quantifier(given) {
            let spec = analyze_quantifier(given, &result.symbolic_types)?;
            result.questionable.extend(spec.questionable);
            result.retained.push(given.clone());
            continue;
        }
        if let Some(variable) = forced_natural
            && !forced_inserted
        {
            if result.symbolic_types.types.contains_key(variable) {
                return Err(format!(
                    "induction-step binder {} collides with its enclosing scope",
                    variable.z3_name()
                ));
            }
            result
                .symbolic_types
                .types
                .insert(variable.clone(), TypeExpr::Nat);
            result.introduced.insert(variable.clone());
            forced_inserted = true;
        }
        let (types, introduced) =
            extend_symbolic_types(&result.symbolic_types, std::slice::from_ref(given))
                .map_err(|error| error.to_string())?;
        result.symbolic_types = types;
        result.introduced.extend(introduced);
        result.ordinary.push(given.clone());
    }
    if let Some(variable) = forced_natural
        && !forced_inserted
    {
        if result.symbolic_types.types.contains_key(variable) {
            return Err(format!(
                "induction-step binder {} collides with its enclosing scope",
                variable.z3_name()
            ));
        }
        result
            .symbolic_types
            .types
            .insert(variable.clone(), TypeExpr::Nat);
        result.introduced.insert(variable.clone());
    }
    Ok(result)
}

pub(super) fn ensure_expression_bound(
    expression: &Expr<()>,
    types: &SymbolicTypeEnvironment,
) -> Result<(), ModelFindingError> {
    if let Some(variable) = free_variables(std::iter::once(expression))
        .into_iter()
        .find(|variable| !types.types.contains_key(variable))
    {
        return Err(ModelFindingError::from(ToZ3Error::from(
            TypeError::MissingType(variable),
        )));
    }
    Ok(())
}

pub(super) fn fixed_assignment_declarations(
    base: &Environment,
    extension_types: &SymbolicTypeEnvironment,
) -> Result<Vec<PreparedExpression>, ArgumentValidationError> {
    let mut extension_types = extension_types.clone();
    for parameter in base.natural_assignment.keys() {
        if let NaturalParameter::Variable(variable) = parameter {
            extension_types
                .types
                .entry(variable.clone())
                .or_insert(TypeExpr::Nat);
        }
    }
    base.natural_assignment
        .iter()
        .map(|(parameter, value)| {
            let expression: Expr<()> = match parameter {
                NaturalParameter::Variable(variable) => {
                    Expr::new(RawExpr::Variable(variable.clone()))
                }
                NaturalParameter::ImplicitDimension(dimension) => {
                    Expr::new(RawExpr::ImplicitDimension(*dimension))
                }
            };
            let equality = Expr::new(RawExpr::CmpChain(CmpChain {
                start: expression,
                assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(*value)))],
            }));
            prepare_expression(&extension_types, &equality, POSITIVE)
                .map_err(ToZ3Error::from)
                .map_err(ModelFindingError::from)
                .map_err(ArgumentValidationError::from)
        })
        .collect()
}

pub(super) fn goal_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    givens: &[PreparedExpression],
    contextual_expressions: &[PreparedExpression],
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let assumptions = declarations
        .iter()
        .chain(givens)
        .cloned()
        .collect::<Vec<_>>();
    let iterator = match extract_prepared_environment_iterator(
        symbolic_types,
        &assumptions,
        contextual_expressions,
        max_dimension,
    ) {
        Ok(iterator) => iterator,
        Err(ShapeError::Unsat(_)) | Err(ShapeError::InvalidTyping(_)) => {
            return Ok(StepEnvironmentExtensions {
                environments: Vec::new(),
                exhaustive: true,
            });
        }
        Err(error) => return Err(error.into()),
    };
    let exhaustive = iterator.dimension_bound_is_exhaustive();
    let environments = iterator.collect::<Result<Vec<_>, _>>()?;
    Ok(StepEnvironmentExtensions {
        environments,
        exhaustive,
    })
}

pub(super) fn quantifier_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    premises: &[PreparedExpression],
    required_body: Option<&PreparedExpression>,
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let assumptions = declarations
        .iter()
        .chain(premises)
        .cloned()
        .collect::<Vec<_>>();
    let required = required_body.map(std::slice::from_ref).unwrap_or_default();
    let iterator = match extract_prepared_environment_iterator_with_required_context(
        symbolic_types,
        &assumptions,
        required,
        &[],
        max_dimension,
    ) {
        Ok(iterator) => iterator,
        Err(ShapeError::Unsat(_) | ShapeError::InvalidTyping(_)) => {
            return Ok(StepEnvironmentExtensions {
                environments: Vec::new(),
                exhaustive: true,
            });
        }
        Err(error) => return Err(error.into()),
    };
    let exhaustive = iterator.dimension_bound_is_exhaustive();
    let environments = iterator.collect::<Result<Vec<_>, _>>()?;
    Ok(StepEnvironmentExtensions {
        environments,
        exhaustive,
    })
}

pub(super) fn expression_environment_extensions(
    base: &Environment,
    symbolic_types: &SymbolicTypeEnvironment,
    steps: &[PreparedExpression],
    max_dimension: u64,
) -> Result<StepEnvironmentExtensions, ArgumentValidationError> {
    let declarations = fixed_assignment_declarations(base, symbolic_types)?;
    let iterator = match extract_prepared_environment_iterator(
        symbolic_types,
        &declarations,
        steps,
        max_dimension,
    ) {
        Ok(iterator) => iterator,
        Err(ShapeError::Unsat(_)) | Err(ShapeError::InvalidTyping(_)) => {
            return Ok(StepEnvironmentExtensions {
                environments: Vec::new(),
                exhaustive: true,
            });
        }
        Err(error) => return Err(error.into()),
    };
    let exhaustive = iterator.dimension_bound_is_exhaustive();
    let environments = iterator
        .collect::<Result<Vec<_>, ShapeError>>()
        .map_err(ArgumentValidationError::from)?;
    Ok(StepEnvironmentExtensions {
        environments,
        exhaustive,
    })
}

pub(super) struct StepEnvironmentExtensions {
    pub(super) environments: Vec<Environment>,
    pub(super) exhaustive: bool,
}

pub(super) fn concrete_declarations(
    symbolic_types: &SymbolicTypeEnvironment,
    environment: &Environment,
) -> Result<Vec<Expr<()>>, ModelFindingError> {
    let mut declarations = symbolic_types
        .types
        .iter()
        .map(|(variable, ty)| {
            let ty = specialize_type(ty, environment)?;
            Ok(Expr::new(RawExpr::Binop(
                Binop::ElementOf,
                Expr::new(RawExpr::Variable(variable.clone())),
                Expr::new(RawExpr::Type(ty)),
            )))
        })
        .collect::<Result<Vec<_>, ModelFindingError>>()?;
    declarations.sort();
    Ok(declarations)
}

fn specialize_type(
    ty: &TypeExpr<()>,
    environment: &Environment,
) -> Result<TypeExpr<()>, ModelFindingError> {
    Ok(match ty {
        TypeExpr::Set(element) => TypeExpr::Set(Box::new(specialize_type(element, environment)?)),
        TypeExpr::Bool => TypeExpr::Bool,
        TypeExpr::Nat => TypeExpr::Nat,
        TypeExpr::Int => TypeExpr::Int,
        TypeExpr::Real => TypeExpr::Real,
        TypeExpr::Matrix(rows, cols) => TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(
                environment
                    .evaluate_natural(rows)
                    .map_err(crate::to_z3::ToZ3Error::from)?,
            )),
            Expr::new(RawExpr::NatLiteral(
                environment
                    .evaluate_natural(cols)
                    .map_err(crate::to_z3::ToZ3Error::from)?,
            )),
        ),
        TypeExpr::Seq(element, length) => {
            let RawExpr::Type(element) = &element.raw else {
                return Err(crate::to_z3::ToZ3Error::InvalidOperands(
                    "sequence element must be a type expression",
                )
                .into());
            };
            TypeExpr::Seq(
                Expr::new(RawExpr::Type(specialize_type(element, environment)?)),
                Expr::new(RawExpr::NatLiteral(
                    environment
                        .evaluate_natural(length)
                        .map_err(crate::to_z3::ToZ3Error::from)?,
                )),
            )
        }
    })
}

pub(super) fn check_step_existence(
    solver: &mut Solver,
    environment: Rc<Environment>,
    symbolic_types: &SymbolicTypeEnvironment,
    side_conditions: &[LoweredSideCondition],
) -> Result<Vec<StepCheck>, ModelFindingError> {
    let mut checks = Vec::new();
    for condition in side_conditions {
        match &condition.existence {
            LoweredExistence::Guaranteed => {}
            LoweredExistence::Assumed => checks.push(StepCheck::AssumedExistence {
                environment: Rc::clone(&environment),
                introduced_variable: crate::Variable::new(condition.display_name.clone()),
            }),
            LoweredExistence::Checkable(assertions) => {
                solver.push();
                for other in side_conditions {
                    if other.introduced_variable != condition.introduced_variable {
                        assert_definitions(solver, std::slice::from_ref(other))?;
                    }
                }
                for assertion in assertions {
                    solver.assert(z3_boolean(assertion)?);
                }
                let result = match solver.check() {
                    SatResult::Unsat => None,
                    SatResult::Unknown => Some(StepCheck::Unknown {
                        environment: Some(Rc::clone(&environment)),
                    }),
                    SatResult::Sat => Some(StepCheck::MayBeUndefined {
                        environment: Rc::clone(&environment),
                        introduced_variable: crate::Variable::new(condition.display_name.clone()),
                        witness: extract_model(
                            &environment,
                            symbolic_types,
                            &solver.get_model().ok_or(ModelFindingError::MissingModel)?,
                        )?,
                    }),
                };
                solver.pop(1);
                if let Some(result) = result {
                    checks.push(result);
                }
            }
        }
    }
    Ok(checks)
}

pub(super) fn core_facts(solver: &Solver, tracked: &[(Bool, Expr<()>)]) -> Vec<Expr<()>> {
    let core = solver.get_unsat_core();
    tracked
        .iter()
        .filter(|(tracker, _)| core.contains(tracker))
        .map(|(_, expression)| expression.clone())
        .collect()
}
