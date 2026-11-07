use super::*;

fn expression(tex: &str) -> Expr<()> {
    crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap()
}
fn variable(name: &str) -> Variable {
    Variable::new(name)
}
fn implication(p: Expr<()>, q: Expr<()>) -> Expr<()> {
    Expr::new(RawExpr::LogicChain(crate::LogicChain {
        start: p,
        assertions: vec![(Logic::Imp, q)],
    }))
}
fn typed(names: &[&str]) -> ProofContext {
    let mut c = ProofContext::default();
    for name in names {
        c.declare_parameter(variable(name), TypeExpr::Real);
    }
    c
}
struct Structural;
impl SideConditionChecker for Structural {
    fn check_instantiation(
        &mut self,
        _: &QuantifierSpec,
        _: &BTreeMap<Variable, Expr<()>>,
        pairs: &BTreeSet<(ImplicitDimension, ImplicitDimension)>,
        _: &[Expr<()>],
    ) -> SideConditionResult {
        if pairs.is_empty() {
            SideConditionResult::Valid
        } else {
            SideConditionResult::Inconclusive("dimension evidence required".into())
        }
    }
}
fn prove(context: &ProofContext, sentence: &Expr<()>) -> Vec<Derivation> {
    match follows_from_natural_deduction(context, sentence, &mut Structural) {
        NaturalDeductionResult::Established { derivations, .. } => derivations,
        other => panic!("expected proof of {}, got {other:?}", sentence.as_latex()),
    }
}
fn accept(context: &mut ProofContext, tex: &str) {
    let e = expression(tex);
    let NaturalDeductionResult::Established {
        conclusion,
        mut derivations,
    } = follows_from_natural_deduction(context, &e, &mut Structural)
    else {
        panic!("expected proof")
    };
    if matches!(
        derivations[0].proof,
        NaturalDeductionProof::ExistentialElimination { .. }
    ) {
        context
            .open_witness(conclusion, Vec::new(), derivations.remove(0))
            .unwrap();
    } else {
        context.record(conclusion, Vec::new(), derivations).unwrap();
    }
}

#[test]
fn existential_introduction_joins_witnesses_and_preserves_sources() {
    let mut c = typed(&["y"]);
    let a = test_assume(&mut c, expression("1 > 0"), Vec::new());
    let b = test_assume(&mut c, expression("1 < y"), Vec::new());
    test_assume(&mut c, expression("2 > 0"), Vec::new());
    let ds = prove(&c, &expression(r"\exists x > 0, x < y"));
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].assumptions, BTreeSet::from([a, b]));
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::ExistentialIntroduction { assignments, .. } if assignments[&variable("x")] == expression("1"))
    );
    assert!(matches!(
        follows_from_natural_deduction(&c, &expression(r"\exists x > 0, x > y"), &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn universal_elimination_requires_existing_restrictions() {
    let mut c = typed(&["y"]);
    test_assume(&mut c, expression(r"\forall x > 0, x < y"), Vec::new());
    let target = expression("1 < y");
    assert!(matches!(
        follows_from_natural_deduction(&c, &target, &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
    test_assume(&mut c, expression("1 > 0"), Vec::new());
    let ds = prove(&c, &target);
    assert!(matches!(
        ds[0].proof,
        NaturalDeductionProof::UniversalElimination { .. }
    ));
    assert_eq!(ds[0].assumptions.len(), 2);
}

#[test]
fn implication_discharges_occurrences_without_mutating_context() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let outer = test_assume(&mut c, p.clone(), Vec::new());
    c.enter_scope();
    let inner = test_assume(&mut c, p.clone(), Vec::new());
    let ds = prove(&c, &implication(p.clone(), p));
    assert!(ds.iter().any(|d| d.assumptions.is_empty()));
    assert!(c.assumptions.contains_key(&outer) && c.assumptions.contains_key(&inner));
}

#[test]
fn conjunction_antecedents_discharge_individual_assumptions() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let q = expression("x < 2");
    test_assume(&mut c, p.clone(), Vec::new());
    test_assume(&mut c, q.clone(), Vec::new());
    test_record_external(&mut c, expression("x < 3"), Vec::new());
    let target = implication(
        Expr::new(RawExpr::Finop(Finop::And, vec![p, q])),
        expression("x < 3"),
    );
    assert!(prove(&c, &target).iter().any(|d| d.assumptions.is_empty()));
}

#[test]
fn universal_introduction_discharges_declarations_but_not_other_dependencies() {
    let mut c = typed(&[]);
    c.enter_scope();
    c.declare_parameter(variable("a"), TypeExpr::Real);
    test_assume(&mut c, expression(r"a \in \mathbb{R}"), Vec::new());
    test_record_external(&mut c, expression("a = a"), Vec::new());
    let target = expression(r"\forall x \in \mathbb{R}, x = x");
    assert!(
        prove(&c, &target)
            .iter()
            .any(|d| d.assumptions.is_empty() && d.required_variables.is_empty())
    );
    let mut bad = typed(&["a"]);
    test_assume(&mut bad, expression("a > 0"), Vec::new());
    test_record_external(&mut bad, expression("a = a"), Vec::new());
    assert!(matches!(
        follows_from_natural_deduction(&bad, &target, &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
    let mut concrete = typed(&[]);
    test_record_external(&mut concrete, expression("1 = 1"), Vec::new());
    assert!(matches!(
        follows_from_natural_deduction(&concrete, &target, &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn witness_discharge_replaces_the_assumption_with_source_dependencies() {
    let mut c = typed(&["y"]);
    let source = test_assume(
        &mut c,
        expression(r"\exists x \in \mathbb{R}, x < y"),
        Vec::new(),
    );
    accept(&mut c, "a < y");
    let witness = c.witnesses[0].assumption;
    test_record_external(&mut c, expression("y = y"), Vec::new());
    let fact = c
        .facts()
        .iter()
        .find(|f| f.expression == expression("y = y"))
        .unwrap();
    assert!(
        fact.derivations
            .iter()
            .any(|d| d.assumptions == BTreeSet::from([source])
                && !d.required_variables.contains(&variable("a"))
                && !d.witness_discharges.is_empty())
    );
    assert!(c.assumptions.contains_key(&witness));
    let target = expression(r"\forall x \in \mathbb{R}, x < y");
    assert!(matches!(
        follows_from_natural_deduction(&c, &target, &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn later_assumptions_can_prevent_witness_discharge() {
    let mut c = typed(&["y"]);
    test_assume(
        &mut c,
        expression(r"\exists x \in \mathbb{R}, x < y"),
        Vec::new(),
    );
    accept(&mut c, "a < y");
    let witness = c.witnesses[0].assumption;
    c.enter_scope();
    test_assume(
        &mut c,
        implication(expression("a < y"), expression("y = 0")),
        Vec::new(),
    );
    test_record_external(&mut c, expression("y = 0"), Vec::new());
    let fact = c
        .facts()
        .iter()
        .find(|f| f.expression == expression("y = 0"))
        .unwrap();
    assert!(
        fact.derivations
            .iter()
            .all(|d| d.assumptions.contains(&witness))
    );
}

#[test]
fn free_witness_and_dependent_type_do_not_escape() {
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\exists n \in \mathbb{N}, n > 0"),
        Vec::new(),
    );
    accept(&mut c, "a > 0");
    let witness = c.witnesses[0].assumption;
    c.declare_parameter(
        variable("v"),
        TypeExpr::Matrix(expression("a"), expression("1")),
    );
    test_record_external(&mut c, expression("v = v"), Vec::new());
    let fact = c
        .facts()
        .iter()
        .find(|f| f.expression == expression("v = v"))
        .unwrap();
    assert!(
        fact.derivations
            .iter()
            .all(|d| d.assumptions.contains(&witness))
    );
}

#[test]
fn independent_derivation_survives_an_earlier_dependent_one() {
    let mut c = typed(&["x"]);
    test_assume(&mut c, expression("x > 0"), Vec::new());
    let parent = c.clone();
    c.enter_scope();
    test_assume(&mut c, expression("x < 2"), Vec::new());
    test_record_external(&mut c, expression("x > 0"), Vec::new());
    assert!(
        c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == expression("x > 0"))
    );
    test_record_external(&mut c, expression("x < 3"), Vec::new());
    assert!(
        !c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == expression("x < 3"))
    );
}

#[test]
fn contextual_conjuncts_are_views_with_provenance() {
    let mut c = typed(&["y"]);
    test_assume(&mut c, expression(r"1 > 0 \land 1 < y"), Vec::new());
    let ds = prove(&c, &expression(r"\exists x > 0, x < y"));
    assert!(
        matches!(&ds[0].proof,NaturalDeductionProof::ExistentialIntroduction { premises, .. } if premises.len()==2 && premises.iter().all(|p| matches!(p, ProofInput::Local { proof, .. } if matches!(**proof, NaturalDeductionProof::ConjunctionElimination { .. }))))
    );
}

#[test]
fn externally_accepted_facts_are_available_as_premises() {
    let mut c = typed(&["x"]);
    test_record_external(&mut c, expression("x = 1"), Vec::new());
    assert!(!prove(&c, &implication(expression("x > 0"), expression("x = 1"))).is_empty());
}

#[test]
fn side_condition_uncertainty_is_not_a_disproof() {
    struct Unknown;
    impl SideConditionChecker for Unknown {
        fn check_instantiation(
            &mut self,
            _: &QuantifierSpec,
            _: &BTreeMap<Variable, Expr<()>>,
            _: &BTreeSet<(ImplicitDimension, ImplicitDimension)>,
            _: &[Expr<()>],
        ) -> SideConditionResult {
            SideConditionResult::Inconclusive("unknown dimensions".into())
        }
    }
    let mut c = typed(&[]);
    test_assume(&mut c, expression("1 > 0"), Vec::new());
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &expression(r"\exists x \in \mathbb{R}, x > 0"),
            &mut Unknown
        ),
        NaturalDeductionResult::Inconclusive { .. }
    ));
}

#[test]
fn universal_introduction_allows_unused_restrictions() {
    let mut c = typed(&["a"]);
    test_assume(&mut c, expression(r"a \in \mathbb{R}"), Vec::new());
    test_record_external(&mut c, expression("a = a"), Vec::new());
    assert!(!prove(&c, &expression(r"\forall x \in \mathbb{R}, x > 0, x = x")).is_empty());
}

#[test]
fn new_free_variables_are_only_introduced_by_witness_opening() {
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\forall x \in \mathbb{R}, x = x"),
        Vec::new(),
    );
    test_record_external(&mut c, expression("1 = 1"), Vec::new());
    for target in [
        expression("a = a"),
        implication(expression("a > 0"), expression("1 = 1")),
    ] {
        assert!(matches!(
            follows_from_natural_deduction(&c, &target, &mut Structural),
            NaturalDeductionResult::Invalid { .. }
        ));
    }
}

#[test]
fn universal_matching_does_not_capture_an_inner_binder() {
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right)"),
        Vec::new(),
    );
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &expression(r"\exists z \in \mathbb{R}, z = z"),
            &mut Structural
        ),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn incomparable_dependencies_are_preserved_and_vacuous_discharge_is_allowed() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let a = test_assume(&mut c, p.clone(), Vec::new());
    c.enter_scope();
    let b = test_assume(&mut c, p.clone(), Vec::new());
    let ds = prove(&c, &p);
    assert_eq!(ds.len(), 2);
    assert!(ds.iter().any(|d| d.assumptions == BTreeSet::from([a])));
    assert!(ds.iter().any(|d| d.assumptions == BTreeSet::from([b])));
    let ds = prove(&c, &implication(expression("x < 0"), p));
    assert!(ds.iter().all(|d| matches!(&d.proof,NaturalDeductionProof::ImplicationIntroduction { discharged,.. } if discharged.is_empty())));
}

#[test]
fn nested_witness_scopes_discharge_in_dependency_order() {
    let mut c = typed(&[]);
    let source = test_assume(
        &mut c,
        expression(r"\exists x \in \mathbb{R}, x > 0"),
        Vec::new(),
    );
    accept(&mut c, "a > 0");
    // An external lemma depending on a licenses a second local witness.
    test_record_external(
        &mut c,
        expression(r"\exists y \in \mathbb{R}, y > a"),
        Vec::new(),
    );
    accept(&mut c, "b > a");
    test_record_external(&mut c, expression("1 = 1"), Vec::new());
    let ds = prove(&c, &expression("1 = 1"));
    assert!(
        ds.iter()
            .any(|d| d.assumptions == BTreeSet::from([source]) && d.required_variables.is_empty())
    );
}

#[test]
fn accepted_symbolic_natural_facts_can_be_generalized() {
    let mut c = ProofContext::default();
    c.declare_parameter(variable("n"), TypeExpr::Nat);
    test_assume(&mut c, expression(r"n \in \mathbb{N}"), Vec::new());
    test_record_external(&mut c, expression("n = 0"), Vec::new());
    assert!(!prove(&c, &expression(r"\forall x \in \mathbb{N}, x = 0")).is_empty());
}

#[test]
fn a_quantifiers_dependent_type_retains_its_outer_dimension_scope() {
    let mut c = typed(&[]);
    test_record_external(&mut c, expression("1 = 1"), Vec::new());
    let parent = c.clone();
    c.enter_scope();
    c.declare_parameter(variable("n"), TypeExpr::Nat);
    test_assume(&mut c, expression(r"n \in \mathbb{N}"), Vec::new());
    let target = implication(
        expression(r"\forall v \in \mathbb{R}^{n}, v = v"),
        expression("1 = 1"),
    );
    let ds = prove(&c, &target);
    assert!(
        ds.iter()
            .all(|d| d.required_variables.contains(&variable("n")))
    );
    test_record(&mut c, target.clone(), Vec::new(), ds);
    assert!(
        !c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == target)
    );
}

#[test]
fn a_witness_used_in_a_quantifiers_domain_cannot_be_discharged() {
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\exists m \in \mathbb{N}, m > 0"),
        Vec::new(),
    );
    accept(&mut c, "n > 0");
    let witness = c.witnesses[0].assumption;
    let conclusion = expression(r"\forall v \in \mathbb{R}^{n}, v = v");
    test_record_external(&mut c, conclusion.clone(), Vec::new());
    let fact = c
        .facts()
        .iter()
        .find(|f| f.expression == conclusion)
        .unwrap();
    assert!(
        fact.derivations
            .iter()
            .all(|d| d.assumptions.contains(&witness))
    );
}

#[test]
fn implication_can_discharge_multiple_occurrences_of_the_same_assumption() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let first = test_assume(&mut c, p.clone(), Vec::new());
    c.enter_scope();
    let second = test_assume(&mut c, p.clone(), Vec::new());
    test_record_external(&mut c, expression("x > -1"), Vec::new());
    let ds = prove(&c, &implication(p, expression("x > -1")));
    assert!(ds.iter().any(|d| d.assumptions.is_empty() && matches!(&d.proof,NaturalDeductionProof::ImplicationIntroduction { discharged, .. } if discharged==&BTreeSet::from([first,second]))));
}

#[test]
fn later_declarations_do_not_reinterpret_a_stored_quantifier() {
    let mut c = typed(&["y"]);
    test_assume(
        &mut c,
        expression(r"\forall x \in \mathbb{R}, x < y"),
        Vec::new(),
    );
    c.declare_parameter(variable("x"), TypeExpr::Real);
    let ds = prove(&c, &expression("x < y"));
    assert!(matches!(
        ds[0].proof,
        NaturalDeductionProof::UniversalElimination { .. }
    ));
}

#[test]
fn nested_binders_stay_bound_after_a_same_named_parameter_is_declared() {
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right)"),
        Vec::new(),
    );
    c.declare_parameter(variable("y"), TypeExpr::Real);
    let ds = prove(&c, &expression(r"\exists z \in \mathbb{R}, y = z"));
    assert!(
        ds.iter()
            .any(|d| matches!(d.proof, NaturalDeductionProof::UniversalElimination { .. }))
    );
}

fn follows_from_natural_deduction(
    context: &ProofContext,
    conclusion: &Expr<()>,
    checks: &mut impl SideConditionChecker,
) -> NaturalDeductionResult {
    super::follows_from_natural_deduction(context, conclusion, &SurfaceInterpreter, checks)
}
fn test_assume(
    context: &mut ProofContext,
    expression: Expr<()>,
    views: Vec<Expr<()>>,
) -> AssumptionId {
    let formula = context.check(&expression).unwrap();
    let views = views.iter().map(|e| context.check(e).unwrap()).collect();
    context.assume(formula, views).unwrap()
}
fn test_record_external(context: &mut ProofContext, expression: Expr<()>, views: Vec<Expr<()>>) {
    let formula = context.check(&expression).unwrap();
    let views = views.iter().map(|e| context.check(e).unwrap()).collect();
    context.record_external(formula, views).unwrap();
}
fn test_record(
    context: &mut ProofContext,
    expression: Expr<()>,
    views: Vec<Expr<()>>,
    derivations: Vec<Derivation>,
) {
    let formula = context.check(&expression).unwrap();
    let views = views.iter().map(|e| context.check(e).unwrap()).collect();
    context.record(formula, views, derivations).unwrap();
}

#[test]
fn checked_acceptance_is_atomic_and_rejects_foreign_inputs() {
    let mut context = typed(&["x"]);
    let before = context.store_counts();
    assert!(context.check(&expression("undefined = 0")).is_err());
    assert_eq!(context.store_counts(), before);
    assert!(context.facts().is_empty());
    assert!(context.assumptions().is_empty());

    let valid = context.check(&expression("x = x")).unwrap();
    let foreign = typed(&["x"]);
    let bad_view = foreign.check(&expression("x = x")).unwrap();
    assert_eq!(
        context.assume(valid, vec![bad_view]),
        Err(ContextError::ForeignStore)
    );
    assert_eq!(context.store_counts(), before);
    assert!(context.facts().is_empty());
    assert!(context.assumptions().is_empty());
}

#[test]
fn contexts_share_records_but_visibility_changes_only_by_export_delta() {
    let mut parent = typed(&["x"]);
    let before = parent.store_counts();
    let mut child = parent.clone();
    child.enter_scope();
    assert!(child.shares_store_with(&parent));
    assert!(child.export_delta(&parent).unwrap().is_empty());
    assert_eq!(parent.store_counts(), before);

    test_assume(&mut child, expression("x > 0"), Vec::new());
    let target = implication(expression("x > 0"), expression("x > 0"));
    let NaturalDeductionResult::Established {
        conclusion,
        derivations,
    } = follows_from_natural_deduction(&child, &target, &mut Structural)
    else {
        panic!()
    };
    let id = child.record(conclusion, Vec::new(), derivations).unwrap();
    let proof = child
        .facts()
        .iter()
        .find(|f| f.id == id)
        .unwrap()
        .derivations[0]
        .id;
    assert!(parent.derivation(proof).is_some());
    assert!(parent.facts().is_empty());
    assert!(matches!(
        follows_from_natural_deduction(&parent, &target, &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
    let delta = child.export_delta(&parent).unwrap();
    assert_eq!(delta.len(), 1);
    let counts = parent.store_counts();
    let original = child.derivation(proof).unwrap();
    assert_eq!(parent.import_delta(delta).unwrap(), 1);
    assert_eq!(parent.store_counts(), counts);
    assert!(std::rc::Rc::ptr_eq(
        &original,
        &parent.derivation(proof).unwrap()
    ));
    assert!(matches!(
        follows_from_natural_deduction(&parent, &target, &mut Structural),
        NaturalDeductionResult::Established { .. }
    ));
    assert!(child.export_delta(&parent).unwrap().is_empty());
}

#[test]
fn exporting_multiple_facts_does_not_copy_or_reregister_proof_records() {
    let mut parent = typed(&[]);
    let empty = parent.clone();
    let mut child = parent.clone();
    child.enter_scope();
    for n in 0..8 {
        test_record_external(&mut child, expression(&format!("{n} = {n}")), Vec::new());
    }
    let before = parent.store_counts();
    let delta = child.export_delta(&parent).unwrap();
    assert_eq!(delta.len(), 8);
    assert_eq!(parent.import_delta(delta).unwrap(), 8);
    assert_eq!(parent.store_counts(), before);
    assert_eq!(parent.facts().len(), 8);
    assert!(child.export_delta(&parent).unwrap().is_empty());

    let other = ProofContext::default();
    assert!(matches!(
        child.export_delta(&other),
        Err(ContextError::ForeignStore)
    ));
    let delta = child.export_delta(&empty).unwrap();
    let mut other = other;
    assert_eq!(other.import_delta(delta), Err(ContextError::ForeignStore));
    assert!(other.facts().is_empty());
}

#[test]
fn superseded_derivations_remain_shared_and_foreign_proofs_are_rejected() {
    let mut context = typed(&["x"]);
    test_assume(&mut context, expression("x > 0"), Vec::new());
    let target = implication(expression("x > 0"), expression("x > 0"));
    test_record_external(&mut context, target.clone(), Vec::new());
    let old = context
        .facts()
        .iter()
        .find(|f| f.expression == target)
        .unwrap()
        .derivations[0]
        .clone();
    let NaturalDeductionResult::Established {
        conclusion,
        derivations,
    } = follows_from_natural_deduction(&context, &target, &mut Structural)
    else {
        panic!()
    };
    context.record(conclusion, Vec::new(), derivations).unwrap();
    assert!(std::rc::Rc::ptr_eq(
        &old,
        &context.derivation(old.id).unwrap()
    ));
    assert!(
        !context
            .facts()
            .iter()
            .find(|f| f.expression == target)
            .unwrap()
            .derivations
            .iter()
            .any(|d| d.id == old.id)
    );

    let mut other = typed(&["x"]);
    let checked = other.check(&target).unwrap();
    let before = other.store_counts();
    assert!(matches!(
        other.record(checked, Vec::new(), vec![(*old).clone()]),
        Err(ContextError::UnknownProof(_))
    ));
    assert_eq!(other.store_counts(), before);
    assert!(other.facts().is_empty());
}

#[test]
fn provisional_witness_types_support_simultaneous_binder_renaming() {
    let mut context = typed(&[]);
    test_assume(
        &mut context,
        expression(r"\exists n \in \mathbb{N}, u \in \mathbb{R}^{n}, u = u \land n > 0"),
        Vec::new(),
    );
    let before = context.store_counts();
    let NaturalDeductionResult::Established {
        conclusion,
        mut derivations,
    } = follows_from_natural_deduction(
        &context,
        &expression(r"n = n \land u > 0"),
        &mut Structural,
    )
    else {
        panic!("expected witness proposal")
    };
    assert_eq!(context.store_counts(), before);
    assert!(!context.types.types.contains_key(&variable("u")));
    assert!(
        matches!(&derivations[0].proof,NaturalDeductionProof::ExistentialElimination{introduced_types,..} if introduced_types[&variable("u")]==TypeExpr::Nat && introduced_types[&variable("n")]==TypeExpr::Matrix(expression("u"),expression("1")))
    );
    context
        .open_witness(conclusion, Vec::new(), derivations.remove(0))
        .unwrap();
    assert_eq!(context.types.types[&variable("u")], TypeExpr::Nat);
}

fn conjunction(operands: Vec<Expr<()>>) -> Expr<()> {
    Expr::new(RawExpr::Finop(Finop::And, operands))
}

#[test]
fn conjunction_rules_preserve_nested_structure_and_source_dependencies() {
    let mut c = typed(&["x", "y", "z"]);
    let source = conjunction(vec![
        expression("x>0"),
        conjunction(vec![expression("y>0"), expression("z>0")]),
    ]);
    let id = test_assume(&mut c, source.clone(), Vec::new());
    let before = c.store_counts();
    let ds = prove(&c, &expression("z>0"));
    let NaturalDeductionProof::ConjunctionElimination {
        operand: 1,
        premise: ProofInput::Local { proof, .. },
    } = &ds[0].proof
    else {
        panic!("{:?}", ds[0]);
    };
    assert!(matches!(
        **proof,
        NaturalDeductionProof::ConjunctionElimination { operand: 1, .. }
    ));
    assert_eq!(ds[0].proof.leaves()[0].expression, source);
    assert_eq!(ds[0].assumptions, BTreeSet::from([id]));
    let target = conjunction(vec![
        expression("z>0"),
        conjunction(vec![expression("x>0"), expression("y>0")]),
    ]);
    let ds = prove(&c, &target);
    let NaturalDeductionProof::ConjunctionIntroduction { premises } = &ds[0].proof else {
        panic!()
    };
    assert_eq!(premises.len(), 2);
    assert!(
        matches!(&premises[1], ProofInput::Local { proof, .. } if matches!(**proof, NaturalDeductionProof::ConjunctionIntroduction { .. }))
    );
    assert_eq!(ds[0].assumptions, BTreeSet::from([id]));
    assert_eq!(c.store_counts(), before);
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &conjunction(vec![expression("x>0"), expression("z<0")]),
            &mut Structural
        ),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn conjunction_assembly_supports_discharge_and_all_quantifier_premise_positions() {
    let mut c = typed(&["a"]);
    let positive = test_assume(&mut c, expression("a>0"), vec![]);
    let upper = test_assume(&mut c, expression("a<2"), vec![]);
    let body = conjunction(vec![expression("a>0"), expression("a<2")]);
    let ds = prove(&c, &implication(expression("a>0"), body));
    assert_eq!(ds[0].assumptions, BTreeSet::from([upper]));
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::ImplicationIntroduction { premise: ProofInput::Local { proof, .. }, discharged, .. }
        if discharged.contains(&positive) && matches!(**proof, NaturalDeductionProof::ConjunctionIntroduction { .. }))
    );
    let ds = prove(&c, &expression(r"\exists x \in \mathbb{R}, x>0 \land x<2"));
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::ExistentialIntroduction { premises, assignments }
        if assignments[&variable("x")] == expression("a") && matches!(&premises[0], ProofInput::Local { proof, .. } if matches!(**proof, NaturalDeductionProof::ConjunctionIntroduction { .. })))
    );
    let mut c = typed(&["a"]);
    test_record_external(&mut c, expression("a=a"), vec![]);
    test_record_external(&mut c, expression(r"a a\ge0"), vec![]);
    let ds = prove(
        &c,
        &expression(r"\forall x \in \mathbb{R}, x=x \land x x\ge0"),
    );
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::UniversalIntroduction { premise: ProofInput::Local { proof, .. }, .. } if matches!(**proof, NaturalDeductionProof::ConjunctionIntroduction { .. }))
    );
    let mut c = typed(&[]);
    test_assume(
        &mut c,
        expression(r"\forall t \in \mathbb{R}, t>0 \land t<2, t=t"),
        vec![],
    );
    test_assume(&mut c, expression("1>0"), vec![]);
    test_assume(&mut c, expression("1<2"), vec![]);
    let ds = prove(&c, &expression("1=1"));
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::UniversalElimination { premises, .. }
        if matches!(&premises[0], ProofInput::Local { proof, .. } if matches!(**proof, NaturalDeductionProof::ConjunctionIntroduction { .. })))
    );
}

#[test]
fn conjunction_matching_shares_substitutions_without_searching_for_missing_facts() {
    let mut c = typed(&[]);
    test_assume(&mut c, expression("1>0"), vec![]);
    test_assume(&mut c, expression("2<3"), vec![]);
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &expression(r"\exists x \in \mathbb{R}, x>0 \land x<3"),
            &mut Structural
        ),
        NaturalDeductionResult::NoMatch { .. }
    ));
    test_assume(&mut c, expression(r"\forall t \in \mathbb{R}, t>0"), vec![]);
    // Deriving 2>0 would require an additional quantifier inference beneath ∧I.
    assert!(matches!(
        follows_from_natural_deduction(&c, &expression(r"2>0 \land 2<3"), &mut Structural),
        NaturalDeductionResult::NoMatch { .. }
    ));
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &expression(r"\exists x \in \mathbb{R}, x=7"),
            &mut Structural
        ),
        NaturalDeductionResult::NoMatch { .. }
    ));
}

#[test]
fn conjunction_alternatives_preserve_independent_discharge_and_export_choices() {
    let mut c = typed(&["x"]);
    let a = test_assume(&mut c, expression("x>0"), vec![]);
    let b = test_assume(&mut c, expression("x<2"), vec![]);
    let ds = prove(&c, &expression(r"x>0 \land x<2"));
    assert_eq!(ds[0].assumptions, BTreeSet::from([a, b]));
    // An independent existing whole conjunction must remain available too.
    let mut independent = typed(&["x"]);
    test_record_external(&mut independent, expression(r"x>0 \land x<2"), vec![]);
    let x = test_assume(&mut independent, expression("x>0"), vec![]);
    let ds = prove(&independent, &expression(r"x>0 \implies x>0 \land x<2"));
    assert!(ds.iter().any(|d| !d.assumptions.contains(&x)));
}

#[test]
fn local_rendering_distinguishes_reuse_kinds_and_never_expands_context_proofs() {
    let mut c = typed(&["x"]);
    let written = expression("x+0>0");
    let meaning = expression("x>0");
    let checked = CheckedFormula::from_interpreted(&c, &written, meaning.clone()).unwrap();
    c.assume(checked, vec![]).unwrap();
    assert!(
        !prove(&c, &meaning)[0]
            .proof
            .details(&meaning)
            .contains("Proof tree:")
    );
    assert!(matches!(
        prove(&c, &meaning)[0].proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Resolved,
            ..
        }
    ));
    let mut c = typed(&["x"]);
    test_assume(&mut c, expression("0<x"), vec![meaning.clone()]);
    assert!(
        prove(&c, &meaning)[0]
            .proof
            .details(&meaning)
            .contains("Proof tree:")
    );
    assert!(matches!(
        prove(&c, &meaning)[0].proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Elaborated,
            ..
        }
    ));
    let mut c = typed(&["x"]);
    test_assume(&mut c, meaning.clone(), vec![]);
    let conclusion = implication(meaning.clone(), meaning.clone());
    let NaturalDeductionResult::Established {
        conclusion: checked,
        derivations,
    } = follows_from_natural_deduction(&c, &conclusion, &mut Structural)
    else {
        panic!()
    };
    assert!(
        derivations[0]
            .proof
            .to_tex(&conclusion)
            .contains("Rightarrow I")
    );
    c.record(checked, vec![], derivations).unwrap();
    let proof = &prove(&c, &conclusion)[0].proof;
    assert!(matches!(
        proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Literal,
            ..
        }
    ));
    let tree = proof.to_tex(&conclusion);
    assert!(!proof.details(&conclusion).contains("Proof tree:"));
    assert_eq!(tree.matches("\\dfrac").count(), 1);
    assert!(!tree.contains("Rightarrow I"));
}

#[test]
fn local_rule_tex_and_details_snapshots() {
    let mut cases = Vec::new();
    let mut c = typed(&[]);
    test_assume(&mut c, expression("1>0"), vec![]);
    test_assume(&mut c, expression("1<2"), vec![]);
    for tex in [
        "1>0",
        r"1>0 \land 1<2",
        r"\exists x>0, x<2",
        r"1>0 \implies 1>0",
    ] {
        let conclusion = expression(tex);
        let proof = &prove(&c, &conclusion)[0].proof;
        cases.push(proof.details(&conclusion));
    }
    let mut c = typed(&[]);
    test_assume(&mut c, expression(r"1>0 \land 1<2"), vec![]);
    cases.push(
        prove(&c, &expression("1<2"))[0]
            .proof
            .details(&expression("1<2")),
    );
    let mut c = typed(&["a"]);
    test_assume(&mut c, expression(r"a \in \mathbb{R}"), vec![]);
    test_record_external(&mut c, expression("a=a"), vec![]);
    let conclusion = expression(r"\forall t \in \mathbb{R}, t=t");
    cases.push(prove(&c, &conclusion)[0].proof.details(&conclusion));
    let mut c = typed(&[]);
    test_assume(&mut c, expression(r"\forall t \in \mathbb{R}, t=t"), vec![]);
    cases.push(
        prove(&c, &expression("1=1"))[0]
            .proof
            .details(&expression("1=1")),
    );
    let mut c = typed(&[]);
    test_assume(&mut c, expression(r"\exists t \in \mathbb{R}, t>0"), vec![]);
    cases.push(
        prove(&c, &expression("a>0"))[0]
            .proof
            .details(&expression("a>0")),
    );
    let mut c = typed(&["x"]);
    let written = expression("x+0>0");
    let conclusion = expression("x>0");
    let checked = CheckedFormula::from_interpreted(&c, &written, conclusion.clone()).unwrap();
    c.assume(checked, vec![]).unwrap();
    cases.push(prove(&c, &conclusion)[0].proof.details(&conclusion));
    let mut c = typed(&["x"]);
    test_assume(&mut c, expression("0<x"), vec![conclusion.clone()]);
    cases.push(prove(&c, &conclusion)[0].proof.details(&conclusion));
    expect_test::expect_file!["snapshots/local_proofs.md"].assert_eq(&cases.join("\n\n---\n\n"));
}

#[test]
fn discharge_labels_distinguish_identical_assumption_occurrences() {
    let mut c = typed(&["x"]);
    test_assume(&mut c, expression("x>0"), vec![]);
    c.enter_scope();
    test_assume(&mut c, expression("x>0"), vec![]);
    let conclusion = implication(expression("x>0"), expression("x>0"));
    let proof = &prove(&c, &conclusion)[0].proof;
    let NaturalDeductionProof::ImplicationIntroduction {
        discharged,
        discharged_formulas,
        ..
    } = proof
    else {
        panic!()
    };
    assert_eq!(discharged.len(), 2);
    assert_eq!(discharged_formulas.len(), 2);
    let tex = proof.to_tex(&conclusion);
    assert!(tex.contains(r"\left[x > 0\right]^{a_{1}}"));
    assert!(!tex.contains(r"\left[x > 0\right]^{a_{1},a_{2}}"));
    assert!(tex.contains(r"\,[a_{1},a_{2}]"));
}

#[test]
fn local_evidence_references_cannot_publish_hidden_context_facts() {
    let mut parent = typed(&["x"]);
    let mut child = parent.clone();
    child.enter_scope();
    test_record_external(&mut child, expression("x>0"), vec![]);
    test_record_external(&mut child, expression("x<2"), vec![]);
    let target = expression(r"x>0 \land x<2");
    let derivations = prove(&child, &target);
    let checked = parent.check(&target).unwrap();
    let before = parent.store_counts();
    assert!(matches!(
        parent.record(checked, vec![], derivations),
        Err(ContextError::InaccessibleProof(_))
    ));
    assert_eq!(parent.store_counts(), before);
    assert!(parent.facts().is_empty());
}

#[test]
fn assumption_external_and_scoped_goal_render_as_established_boundaries() {
    let mut c = typed(&[]);
    let conclusion = expression("1>0");
    let assumption = test_assume(&mut c, conclusion.clone(), vec![]);
    for proof in [
        NaturalDeductionProof::Assumption { assumption },
        NaturalDeductionProof::External,
        NaturalDeductionProof::ScopedGoal {
            givens: vec![conclusion.clone()],
            conclusion: conclusion.clone(),
            cases: vec![c.facts()[0].derivations[0].id],
        },
    ] {
        assert_eq!(proof.to_tex(&conclusion), "1 > 0");
    }
}
