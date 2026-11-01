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
        NaturalDeductionResult::Established { derivations } => derivations,
        other => panic!("expected proof of {}, got {other:?}", sentence.as_latex()),
    }
}
fn accept(context: &mut ProofContext, tex: &str) {
    let e = expression(tex);
    let d = prove(context, &e);
    context.record(e, Vec::new(), d);
}

#[test]
fn existential_introduction_joins_witnesses_and_preserves_sources() {
    let mut c = typed(&["y"]);
    let a = c.assume(expression("1 > 0"), Vec::new());
    let b = c.assume(expression("1 < y"), Vec::new());
    c.assume(expression("2 > 0"), Vec::new());
    let ds = prove(&c, &expression(r"\exists x > 0, x < y"));
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].assumptions, BTreeSet::from([a, b]));
    assert!(
        matches!(&ds[0].proof, NaturalDeductionProof::ExistentialIntroduction { assignments, .. } if assignments[&variable("x")] == expression("1"))
    );
    assert!(matches!(
        follows_from_natural_deduction(&c, &expression(r"\exists x > 0, x > y"), &mut Structural),
        NaturalDeductionResult::NoMatch
    ));
}

#[test]
fn universal_elimination_requires_existing_restrictions() {
    let mut c = typed(&["y"]);
    c.assume(expression(r"\forall x > 0, x < y"), Vec::new());
    let target = expression("1 < y");
    assert!(matches!(
        follows_from_natural_deduction(&c, &target, &mut Structural),
        NaturalDeductionResult::NoMatch
    ));
    c.assume(expression("1 > 0"), Vec::new());
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
    let outer = c.assume(p.clone(), Vec::new());
    c.enter_scope();
    let inner = c.assume(p.clone(), Vec::new());
    let ds = prove(&c, &implication(p.clone(), p));
    assert!(ds.iter().any(|d| d.assumptions.is_empty()));
    assert!(c.assumptions.contains_key(&outer) && c.assumptions.contains_key(&inner));
}

#[test]
fn conjunction_antecedents_discharge_individual_assumptions() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let q = expression("x < 2");
    c.assume(p.clone(), Vec::new());
    c.assume(q.clone(), Vec::new());
    c.record_external(expression("x < 3"), Vec::new());
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
    c.assume(expression(r"a \in \mathbb{R}"), Vec::new());
    c.record_external(expression("a = a"), Vec::new());
    let target = expression(r"\forall x \in \mathbb{R}, x = x");
    assert!(
        prove(&c, &target)
            .iter()
            .any(|d| d.assumptions.is_empty() && d.required_variables.is_empty())
    );
    let mut bad = typed(&["a"]);
    bad.assume(expression("a > 0"), Vec::new());
    bad.record_external(expression("a = a"), Vec::new());
    assert!(matches!(
        follows_from_natural_deduction(&bad, &target, &mut Structural),
        NaturalDeductionResult::NoMatch
    ));
    let mut concrete = typed(&[]);
    concrete.record_external(expression("1 = 1"), Vec::new());
    assert!(matches!(
        follows_from_natural_deduction(&concrete, &target, &mut Structural),
        NaturalDeductionResult::NoMatch
    ));
}

#[test]
fn witness_discharge_replaces_the_assumption_with_source_dependencies() {
    let mut c = typed(&["y"]);
    let source = c.assume(expression(r"\exists x \in \mathbb{R}, x < y"), Vec::new());
    accept(&mut c, "a < y");
    let witness = c.witnesses[0].assumption;
    c.record_external(expression("y = y"), Vec::new());
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
        NaturalDeductionResult::NoMatch
    ));
}

#[test]
fn later_assumptions_can_prevent_witness_discharge() {
    let mut c = typed(&["y"]);
    c.assume(expression(r"\exists x \in \mathbb{R}, x < y"), Vec::new());
    accept(&mut c, "a < y");
    let witness = c.witnesses[0].assumption;
    c.enter_scope();
    c.assume(
        implication(expression("a < y"), expression("y = 0")),
        Vec::new(),
    );
    c.record_external(expression("y = 0"), Vec::new());
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
    c.assume(expression(r"\exists n \in \mathbb{N}, n > 0"), Vec::new());
    accept(&mut c, "a > 0");
    let witness = c.witnesses[0].assumption;
    c.declare_parameter(
        variable("v"),
        TypeExpr::Matrix(expression("a"), expression("1")),
    );
    c.record_external(expression("v = v"), Vec::new());
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
    c.assume(expression("x > 0"), Vec::new());
    let parent = c.clone();
    c.enter_scope();
    c.assume(expression("x < 2"), Vec::new());
    c.record_external(expression("x > 0"), Vec::new());
    assert!(
        c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == expression("x > 0"))
    );
    c.record_external(expression("x < 3"), Vec::new());
    assert!(
        !c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == expression("x < 3"))
    );
}

#[test]
fn contextual_conjuncts_are_views_with_provenance() {
    let mut c = typed(&["y"]);
    c.assume(expression(r"1 > 0 \land 1 < y"), Vec::new());
    let ds = prove(&c, &expression(r"\exists x > 0, x < y"));
    assert!(
        matches!(&ds[0].proof,NaturalDeductionProof::ExistentialIntroduction { premises, .. } if premises.len()==2 && premises.iter().all(|p| p.conjunct > 0))
    );
}

#[test]
fn externally_accepted_facts_are_available_as_premises() {
    let mut c = typed(&["x"]);
    c.record_external(expression("x = 1"), Vec::new());
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
    c.assume(expression("1 > 0"), Vec::new());
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
    c.assume(expression(r"a \in \mathbb{R}"), Vec::new());
    c.record_external(expression("a = a"), Vec::new());
    assert!(!prove(&c, &expression(r"\forall x \in \mathbb{R}, x > 0, x = x")).is_empty());
}

#[test]
fn new_free_variables_are_only_introduced_by_witness_opening() {
    let mut c = typed(&[]);
    c.assume(expression(r"\forall x \in \mathbb{R}, x = x"), Vec::new());
    c.record_external(expression("1 = 1"), Vec::new());
    for target in [
        expression("a = a"),
        implication(expression("a > 0"), expression("1 = 1")),
    ] {
        assert!(matches!(
            follows_from_natural_deduction(&c, &target, &mut Structural),
            NaturalDeductionResult::NoMatch
        ));
    }
}

#[test]
fn universal_matching_does_not_capture_an_inner_binder() {
    let mut c = typed(&[]);
    c.assume(
        expression(r"\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right)"),
        Vec::new(),
    );
    assert!(matches!(
        follows_from_natural_deduction(
            &c,
            &expression(r"\exists z \in \mathbb{R}, z = z"),
            &mut Structural
        ),
        NaturalDeductionResult::NoMatch
    ));
}

#[test]
fn incomparable_dependencies_are_preserved_and_vacuous_discharge_is_allowed() {
    let mut c = typed(&["x"]);
    let p = expression("x > 0");
    let a = c.assume(p.clone(), Vec::new());
    c.enter_scope();
    let b = c.assume(p.clone(), Vec::new());
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
    let source = c.assume(expression(r"\exists x \in \mathbb{R}, x > 0"), Vec::new());
    accept(&mut c, "a > 0");
    // An external lemma depending on a licenses a second local witness.
    c.record_external(expression(r"\exists y \in \mathbb{R}, y > a"), Vec::new());
    accept(&mut c, "b > a");
    c.record_external(expression("1 = 1"), Vec::new());
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
    c.assume(expression(r"n \in \mathbb{N}"), Vec::new());
    c.record_external(expression("n = 0"), Vec::new());
    assert!(!prove(&c, &expression(r"\forall x \in \mathbb{N}, x = 0")).is_empty());
}

#[test]
fn a_quantifiers_dependent_type_retains_its_outer_dimension_scope() {
    let mut c = typed(&[]);
    c.record_external(expression("1 = 1"), Vec::new());
    let parent = c.clone();
    c.enter_scope();
    c.declare_parameter(variable("n"), TypeExpr::Nat);
    c.assume(expression(r"n \in \mathbb{N}"), Vec::new());
    let target = implication(
        expression(r"\forall v \in \mathbb{R}^{n}, v = v"),
        expression("1 = 1"),
    );
    let ds = prove(&c, &target);
    assert!(
        ds.iter()
            .all(|d| d.required_variables.contains(&variable("n")))
    );
    c.record(target.clone(), Vec::new(), ds);
    assert!(
        !c.exportable_to(&parent)
            .iter()
            .any(|f| f.expression == target)
    );
}

#[test]
fn a_witness_used_in_a_quantifiers_domain_cannot_be_discharged() {
    let mut c = typed(&[]);
    c.assume(expression(r"\exists m \in \mathbb{N}, m > 0"), Vec::new());
    accept(&mut c, "n > 0");
    let witness = c.witnesses[0].assumption;
    let conclusion = expression(r"\forall v \in \mathbb{R}^{n}, v = v");
    c.record_external(conclusion.clone(), Vec::new());
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
    let first = c.assume(p.clone(), Vec::new());
    c.enter_scope();
    let second = c.assume(p.clone(), Vec::new());
    c.record_external(expression("x > -1"), Vec::new());
    let ds = prove(&c, &implication(p, expression("x > -1")));
    assert!(ds.iter().any(|d| d.assumptions.is_empty() && matches!(&d.proof,NaturalDeductionProof::ImplicationIntroduction { discharged, .. } if discharged==&BTreeSet::from([first,second]))));
}

#[test]
fn later_declarations_do_not_reinterpret_a_stored_quantifier() {
    let mut c = typed(&["y"]);
    c.assume(expression(r"\forall x \in \mathbb{R}, x < y"), Vec::new());
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
    c.assume(
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
