use super::*;

struct WitnessMatch {
    assignments: BTreeMap<Variable, Expr<()>>,
    supporting_facts: Vec<Expr<()>>,
    nonce_pairs: BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
}

pub(super) struct DimensionChecks<'a> {
    pub context: &'a crate::natural_deduction::ProofContext,
    pub givens: &'a [PreparedExpression],
    pub timings: &'a Timings,
    pub evidence: Vec<crate::natural_deduction::DerivationId>,
}
impl crate::natural_deduction::SideConditionChecker for DimensionChecks<'_> {
    fn premise_derivations(&self) -> &[crate::natural_deduction::DerivationId] {
        &self.evidence
    }
    fn check_instantiation(
        &mut self,
        spec: &QuantifierSpec,
        assignments: &BTreeMap<Variable, Expr<()>>,
        nonce_pairs: &BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
        supporting_facts: &[Expr<()>],
    ) -> crate::natural_deduction::SideConditionResult {
        self.evidence.clear();
        // Identical types and scalar promotions require no contextual dimension
        // assumptions and therefore add no scope dependencies.
        if nonce_pairs.is_empty()
            && assignments.iter().all(|(v, term)| {
                let Ok(analyzed) =
                    crate::type_resolver::analyze_expression(&self.context.types, term)
                else {
                    return false;
                };
                let Ok(actual) = analyzed.meta.get_type() else {
                    return false;
                };
                let expected = &spec.bindings[v];
                *expected == actual
                    || matches!(
                        (expected, actual),
                        (TypeExpr::Real, TypeExpr::Nat | TypeExpr::Int)
                            | (TypeExpr::Int, TypeExpr::Nat)
                    )
            })
        {
            return crate::natural_deduction::SideConditionResult::Valid;
        }
        let natural_symbols = self
            .context
            .types
            .types
            .iter()
            .filter(|(_, t)| **t == TypeExpr::Nat)
            .map(|(v, _)| {
                (
                    NaturalParameter::Variable(v.clone()),
                    z3::ast::Int::new_const(v.z3_name()),
                )
            })
            .collect();
        let mut assumptions = self.givens.to_vec();
        for fact in self.context.facts() {
            let is_assumption = fact.derivations.iter().any(|d| {
                matches!(
                    d.proof,
                    crate::natural_deduction::NaturalDeductionProof::Assumption { .. }
                )
            });
            let natural_constraints = crate::formula::conjunction_views(&fact.expression)
                .into_iter()
                .filter(|expression| {
                    let RawExpr::CmpChain(chain) = &expression.raw else {
                        return false;
                    };
                    std::iter::once(&chain.start)
                        .chain(chain.assertions.iter().map(|(_, e)| e))
                        .all(|term| {
                            matches!(
                                crate::z3_utils::classify_presburger(term, &natural_symbols),
                                crate::z3_utils::PresburgerClassification::Valid
                            )
                        })
                })
                .collect::<Vec<_>>();
            let is_natural = !natural_constraints.is_empty();
            for expression in natural_constraints {
                if let Ok(prepared) = prepare_expression(&self.context.types, expression, POSITIVE)
                {
                    assumptions.push(prepared);
                }
            }
            if (is_assumption || is_natural)
                && let Some(d) = fact.derivations.first()
            {
                self.evidence.push(d.id);
            }
        }
        let witness = WitnessMatch {
            assignments: assignments.clone(),
            supporting_facts: supporting_facts.to_vec(),
            nonce_pairs: nonce_pairs.clone(),
        };
        use crate::natural_deduction::SideConditionResult;
        match witness_dimension_result(
            spec,
            &self.context.types,
            &assumptions,
            &witness,
            self.timings,
        ) {
            Ok(true) => SideConditionResult::Valid,
            Ok(false)
            | Err(ArgumentValidationError::Shape(
                ShapeError::Unsat(_) | ShapeError::InvalidTyping(_),
            )) => SideConditionResult::Invalid,
            Err(error) => SideConditionResult::Inconclusive(error.to_string()),
        }
    }
}

fn witness_dimension_result(
    spec: &QuantifierSpec,
    active_types: &SymbolicTypeEnvironment,
    givens: &[PreparedExpression],
    witness: &WitnessMatch,
    timings: &Timings,
) -> Result<bool, ArgumentValidationError> {
    let mut types = active_types.clone();
    types.types.extend(spec.bindings.clone());
    let prepare = |expression: &Expr<()>| {
        prepare_expression(&types, expression, POSITIVE)
            .map_err(ToZ3Error::from)
            .map_err(ModelFindingError::from)
            .map_err(ArgumentValidationError::from)
    };
    let mut assumptions = givens.to_vec();
    assumptions.extend(
        spec.premises
            .iter()
            .map(&prepare)
            .collect::<Result<Vec<_>, _>>()?,
    );
    // Compatibility must follow from the symbolic scope, not from assuming
    // the very binder/term equality whose dimensions we are checking.
    let mut type_query =
        crate::enumerable_envspec::dimension_equivalence_query(&types, &assumptions, &[], timings)?;
    let mut rigid = active_types.types.keys().cloned().collect::<BTreeSet<_>>();
    for ty in active_types.types.values() {
        rigid.extend(free_variables(std::iter::once(&Expr::new(RawExpr::Type(
            ty.clone(),
        )))));
    }
    rigid.extend(spec.introduced.iter().cloned());
    let flexible = spec
        .bindings
        .values()
        .flat_map(|ty| free_variables(std::iter::once(&Expr::new(RawExpr::Type(ty.clone())))))
        .filter(|v| !rigid.contains(v))
        .collect::<BTreeSet<_>>();
    let mut dimensions = BTreeMap::new();
    for (variable, term) in &witness.assignments {
        let actual = crate::type_resolver::analyze_expression(active_types, term)
            .map_err(ModelFindingError::from_type)?
            .meta
            .get_type()
            .map_err(ModelFindingError::from_type)?;
        let expected = crate::formula::substitute_free_variables(
            &Expr::new(RawExpr::Type(spec.bindings[variable].clone())),
            &witness.assignments,
        );
        let RawExpr::Type(expected) = &expected.raw else {
            unreachable!()
        };
        if !compatible_types(
            expected,
            &actual,
            &mut type_query,
            &flexible,
            &mut dimensions,
        )? {
            return Ok(false);
        }
    }
    if witness.nonce_pairs.is_empty() {
        return Ok(true);
    }
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
        &types,
        &assumptions,
        &required,
        timings,
    )?;
    nonce_relationships_result(&mut query, &witness.nonce_pairs).ok_or_else(|| {
        ShapeError::Unknown("could not decide dimension relationships".to_owned()).into()
    })
}

fn compatible_types(
    expected: &TypeExpr<()>,
    actual: &TypeExpr<()>,
    query: &mut crate::enumerable_envspec::DimensionEquivalenceQuery,
    flexible: &BTreeSet<Variable>,
    dimensions: &mut BTreeMap<Variable, Expr<()>>,
) -> Result<bool, ArgumentValidationError> {
    fn equal(
        a: &Expr<()>,
        b: &Expr<()>,
        q: &mut crate::enumerable_envspec::DimensionEquivalenceQuery,
        flexible: &BTreeSet<Variable>,
        dimensions: &mut BTreeMap<Variable, Expr<()>>,
    ) -> Result<bool, ArgumentValidationError> {
        if let RawExpr::Variable(v) = &a.raw
            && flexible.contains(v)
        {
            if let Some(previous) = dimensions.get(v).cloned() {
                return equal(&previous, b, q, &BTreeSet::new(), dimensions);
            }
            dimensions.insert(v.clone(), b.clone());
            return Ok(true);
        }
        match q.necessarily_equal_expressions(a, b) {
            Some(true) => Ok(true),
            Some(false)
                if free_variables(std::iter::once(a).chain(std::iter::once(b))).is_empty() =>
            {
                Ok(false)
            }
            _ => Err(ShapeError::Unknown(
                "dimension compatibility is not established by the symbolic context".into(),
            )
            .into()),
        }
    }
    if expected == actual {
        return Ok(true);
    }
    match (expected, actual) {
        (TypeExpr::Real, TypeExpr::Int | TypeExpr::Nat) | (TypeExpr::Int, TypeExpr::Nat) => {
            Ok(true)
        }
        (TypeExpr::Matrix(a, b), TypeExpr::Matrix(c, d)) => {
            Ok(equal(a, c, query, flexible, dimensions)?
                && equal(b, d, query, flexible, dimensions)?)
        }
        (TypeExpr::Matrix(a, b), TypeExpr::Real | TypeExpr::Int | TypeExpr::Nat)
        | (TypeExpr::Real, TypeExpr::Matrix(a, b)) => {
            let one = Expr::new(RawExpr::NatLiteral(1));
            Ok(equal(a, &one, query, flexible, dimensions)?
                && equal(b, &one, query, flexible, dimensions)?)
        }
        (TypeExpr::Set(a), TypeExpr::Set(b)) => compatible_types(a, b, query, flexible, dimensions),
        (TypeExpr::Seq(a, n), TypeExpr::Seq(b, m)) => {
            let (RawExpr::Type(a), RawExpr::Type(b)) = (&a.raw, &b.raw) else {
                return Ok(false);
            };
            Ok(equal(n, m, query, flexible, dimensions)?
                && compatible_types(a, b, query, flexible, dimensions)?)
        }
        _ => Ok(false),
    }
}

#[cfg(test)]
fn nonce_relationships_match(
    query: &mut crate::enumerable_envspec::DimensionEquivalenceQuery,
    pairs: &BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
) -> bool {
    nonce_relationships_result(query, pairs).unwrap_or(false)
}

fn nonce_relationships_result(
    query: &mut crate::enumerable_envspec::DimensionEquivalenceQuery,
    pairs: &BTreeSet<(crate::ImplicitDimension, crate::ImplicitDimension)>,
) -> Option<bool> {
    let pairs = pairs.iter().copied().collect::<Vec<_>>();
    for (index, (pattern, candidate)) in pairs.iter().enumerate() {
        for (other_pattern, other_candidate) in &pairs[index + 1..] {
            let pattern_equal = query.necessarily_equal(*pattern, *other_pattern)?;
            let candidate_equal = query.necessarily_equal(*candidate, *other_candidate)?;
            if pattern_equal != candidate_equal {
                return Some(false);
            }
        }
    }
    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ImplicitDimension;

    fn dimension(dimension: ImplicitDimension) -> Expr<()> {
        Expr::new(RawExpr::ImplicitDimension(dimension))
    }

    fn equality(left: ImplicitDimension, right: ImplicitDimension) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: dimension(left),
            assertions: vec![(Cmp::Eq, dimension(right))],
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
        crate::enumerable_envspec::dimension_equivalence_query(
            &types,
            &prepared,
            &[],
            &Timings::default(),
        )
        .unwrap()
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
}
