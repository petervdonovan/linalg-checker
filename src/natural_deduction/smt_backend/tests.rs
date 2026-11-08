use super::*;
use crate::{Cmp, CmpChain, Monop};

fn atom(name: &str) -> Expr<()> {
    Expr::new(RawExpr::Variable(Variable::new(name)))
}
fn and(xs: Vec<Expr<()>>) -> Expr<()> {
    Expr::new(RawExpr::Finop(Finop::And, xs))
}
fn context(facts: &[Expr<()>]) -> ProofContext {
    let mut c = ProofContext::default();
    for name in ["p", "q", "r", "s"] {
        c.declare_parameter(Variable::new(name), TypeExpr::Bool);
    }
    for fact in facts {
        let checked = c.check(fact).unwrap();
        c.assume(checked, vec![]).unwrap();
    }
    c
}
fn limits(n: usize, capacity: usize) -> SearchLimits {
    SearchLimits {
        max_rule_slots: n,
        max_premises: capacity,
        timeout_ms: None,
    }
}
fn search(
    c: &ProofContext,
    goal: &Expr<()>,
    n: usize,
    capacity: usize,
) -> Result<(CheckedFormula, Derivation), SearchError> {
    find_proof(c, goal, &SurfaceInterpreter, limits(n, capacity))
}
fn replay_input(c: &ProofContext, input: &ProofInput) -> Expr<()> {
    match input {
        ProofInput::Context(p) => {
            let fact = c
                .facts()
                .iter()
                .find(|f| f.id() == p.fact)
                .expect("contextual leaf is visible");
            assert!(fact.derivations().any(|d| d.id == p.derivation));
            assert_eq!(p.expression, *fact.formula().written());
            assert_eq!(p.conjunct, 0);
            assert_eq!(p.alternative, None);
            fact.formula().meaning()
        }
        ProofInput::Local { conclusion, proof } => {
            replay(c, proof, conclusion);
            conclusion.clone()
        }
    }
}
fn replay(c: &ProofContext, proof: &NaturalDeductionProof, conclusion: &Expr<()>) {
    match proof {
        NaturalDeductionProof::Reuse { premise, .. } => {
            assert_eq!(replay_input(c, premise), *conclusion)
        }
        NaturalDeductionProof::ConjunctionIntroduction { premises } => {
            assert!(!premises.is_empty());
            assert_eq!(
                and(premises.iter().map(|p| replay_input(c, p)).collect()),
                *conclusion
            );
        }
        other => panic!("unexpected rule: {other:?}"),
    }
}

#[test]
fn search_returns_local_existing_evidence_and_does_not_commit_it() {
    let mut c = context(&[atom("p")]);
    // External facts include facts a validator admitted as likely: verification
    // qualifications intentionally are not stored or propagated in ProofContext.
    let checked = c.check(&atom("q")).unwrap();
    c.record_external(checked, vec![]).unwrap();
    let before = c.store_counts();
    let goal = and(vec![atom("p"), atom("q")]);
    let (checked, d) = search(&c, &goal, 1, 3).unwrap();
    assert!(matches!(
        d.proof,
        NaturalDeductionProof::ConjunctionIntroduction { .. }
    ));
    replay(&c, &d.proof, &goal);
    assert_eq!(d.assumptions, c.assumptions().keys().copied().collect());
    assert_eq!(c.store_counts(), before);
    assert_eq!(c.facts().len(), 2);
    c.record(checked, vec![], vec![d]).unwrap();
    assert_eq!(c.facts().len(), 3);
    let (_, reuse) = search(&c, &goal, 0, 0).unwrap();
    assert!(matches!(
        reuse.proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Literal,
            ..
        }
    ));
    assert!(!reuse.proof.details(&goal).contains("Proof tree:"));
}

#[test]
fn source_selection_is_first_visible_whole_fact_and_keeps_bindings() {
    let c = context(&[atom("p"), atom("p")]);
    let first = c.facts()[0].derivations().next().unwrap();
    let (_, d) = search(&c, &atom("p"), 0, 3).unwrap();
    assert_eq!(d.proof.leaves()[0].derivation, first.id);
    assert_eq!(d.assumptions, first.assumptions);
    let mut c = context(&[]);
    let written = atom("q");
    let checked = CheckedFormula::from_interpreted(&c, &written, atom("p")).unwrap();
    c.assume(checked, vec![]).unwrap();
    let (_, d) = search(&c, &atom("p"), 0, 3).unwrap();
    assert!(matches!(
        d.proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Resolved,
            ..
        }
    ));
    assert_eq!(d.proof.supporting_facts(), vec![written]);
    let checked = c.check(&atom("q")).unwrap();
    let view = c.check(&atom("r")).unwrap();
    c.assume(checked, vec![view]).unwrap();
    assert!(matches!(
        search(&c, &atom("r"), 2, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let mut child = c.clone();
    child.enter_scope();
    let new = child.check(&atom("s")).unwrap();
    child.assume(new, vec![]).unwrap();
    assert!(search(&child, &atom("s"), 0, 3).is_ok());
    assert!(matches!(
        search(&c, &atom("s"), 0, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
}

#[test]
fn sharing_and_bfs_numbering_bound_distinct_reachable_inferences() {
    let c = context(&[atom("p"), atom("q"), atom("r"), atom("s")]);
    let shared = and(vec![atom("p"), atom("q")]);
    let twice = and(vec![shared.clone(), shared.clone()]);
    assert!(matches!(
        search(&c, &twice, 1, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = search(&c, &twice, 2, 3).unwrap();
    replay(&c, &d.proof, &twice);
    let goal = and(vec![
        and(vec![shared.clone(), atom("r")]),
        and(vec![shared, atom("s")]),
    ]);
    // Canonical BFS order is root, L, R, C. The shared descendant counts once.
    assert!(matches!(
        search(&c, &goal, 3, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = search(&c, &goal, 4, 3).unwrap();
    replay(&c, &d.proof, &goal);
}

#[test]
fn bounds_preserve_nary_structure_and_do_not_add_elimination() {
    let c = context(&[atom("p"), atom("q"), atom("r")]);
    let flat = and(vec![atom("p"), atom("q"), atom("r")]);
    assert!(matches!(
        search(&c, &flat, 3, 2),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    replay(&c, &search(&c, &flat, 1, 3).unwrap().1.proof, &flat);
    let nested = and(vec![atom("p"), and(vec![atom("q"), atom("r")])]);
    assert!(matches!(
        search(&c, &nested, 1, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    replay(&c, &search(&c, &nested, 2, 3).unwrap().1.proof, &nested);
    assert!(matches!(
        search(&c, &and(vec![atom("p"), atom("s")]), 3, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let c = context(&[and(vec![atom("p"), atom("q")])]);
    assert!(matches!(
        search(&c, &atom("p"), 3, 3),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    // A whole contextual formula needs no construction capacity.
    assert!(search(&c, &and(vec![atom("p"), atom("q")]), 0, 0).is_ok());
}

#[test]
fn options_analysis_encoding_and_solver_failures_are_distinct() {
    let c = context(&[]);
    assert!(matches!(
        find_proof(
            &c,
            &atom("p"),
            &SurfaceInterpreter,
            SearchLimits {
                timeout_ms: Some(0),
                ..limits(1, 3)
            }
        ),
        Err(SearchError::InvalidOptions(_))
    ));
    assert!(matches!(
        search(&c, &atom("undefined"), 1, 3),
        Err(SearchError::InvalidConclusion(_))
    ));
    let l = limits(1, 3);
    assert!(
        matches!(check_status(SatResult::Unsat,None,l),Err(SearchError::NoProofWithinBounds(found)) if found==l)
    );
    assert!(
        matches!(check_status(SatResult::Unknown,Some("timeout".into()),l),Err(SearchError::Timeout { reason }) if reason=="timeout")
    );
    assert!(
        matches!(check_status(SatResult::Unknown,Some("resource limit".into()),l),Err(SearchError::Unknown { reason }) if reason=="resource limit")
    );
    assert!(matches!(
        check_status(SatResult::Unknown, None, l),
        Err(SearchError::Unknown { .. })
    ));
    assert!(check_status(SatResult::Sat, None, l).is_ok());
    let mut c = context(&[atom("p")]);
    c.declare_parameter(
        Variable::new("v"),
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(2)),
            Expr::new(RawExpr::NatLiteral(1)),
        ),
    );
    let norm = Expr::new(RawExpr::Monop(Monop::Norm2, atom("v")));
    let formula = Expr::new(RawExpr::CmpChain(CmpChain {
        start: norm.clone(),
        assertions: vec![(Cmp::Eq, norm)],
    }));
    let checked = c.check(&formula).unwrap();
    c.assume(checked, vec![]).unwrap();
    let before = c.store_counts();
    assert!(matches!(
        search(&c, &atom("p"), 0, 3),
        Err(SearchError::Encoding(smt_dt::Error::Unsupported(_)))
    ));
    assert_eq!(c.store_counts(), before);
    assert!(matches!(
        search(&c, &formula, 0, 3),
        Err(SearchError::Encoding(smt_dt::Error::Unsupported(_)))
    ));
}

#[test]
fn decoding_rejects_malformed_and_inconsistent_models() {
    let c = context(&[atom("p"), atom("q")]);
    let goal = and(vec![atom("p"), atom("q")]);
    let mut query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 3)).unwrap();
    assert!(matches!(
        query.decode_value(&query.proofs.unused(), 1),
        Err(SearchError::InvalidModel(_))
    ));
    assert!(matches!(
        query.decode_value(&query.proofs.constant("unassigned"), 1),
        Err(SearchError::InvalidModel(_))
    ));
    assert!(matches!(
        query.decode_value(&query.expressions.constant("not_a_proof"), 1),
        Err(SearchError::InvalidModel(_))
    ));
    let mut other = ExprDatatype::new("decode_foreign_expr");
    let other_proof = ProofDatatype::new("decode_foreign_proof", &other);
    let foreign = other_proof
        .context(&other.encode(&atom("p")).unwrap())
        .unwrap();
    assert!(matches!(
        query.decode_value(&foreign, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let r = query.expressions.encode(&atom("r")).unwrap();
    let unknown = query.proofs.context(&r).unwrap();
    assert!(matches!(
        query.decode_value(&unknown, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let conclusion_p = query
        .proofs
        .conclusion(&query.leaves[0].value)
        .unwrap()
        .simplify();
    assert!(matches!(
        query.decode_value(
            &query
                .proofs
                .inference(
                    &query.target,
                    ProofRule::AndIntroduction,
                    &[query.leaves[0].value.clone(), query.leaves[1].value.clone()]
                )
                .unwrap(),
            0
        ),
        Err(SearchError::InvalidModel(_))
    ));
    let invalid = query
        .proofs
        .inference(
            &conclusion_p,
            ProofRule::AndIntroduction,
            &[query.leaves[0].value.clone(), query.leaves[1].value.clone()],
        )
        .unwrap();
    assert!(matches!(
        query.decode_value(&invalid, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let empty = query
        .proofs
        .inference(&query.target, ProofRule::AndIntroduction, &[])
        .unwrap();
    assert!(matches!(
        query.decode_value(&empty, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let unused = query
        .proofs
        .inference(
            &query.target,
            ProofRule::AndIntroduction,
            &[query.proofs.unused()],
        )
        .unwrap();
    assert!(matches!(
        query.decode_value(&unused, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let oversized = query
        .proofs
        .inference(
            &query.target,
            ProofRule::AndIntroduction,
            &vec![query.leaves[0].value.clone(); 4],
        )
        .unwrap();
    assert!(matches!(
        query.decode_value(&oversized, 1),
        Err(SearchError::InvalidModel(_))
    ));
    assert_eq!(query.solver.check(), SatResult::Sat);
    assert!(query.decode(&query.solver.get_model().unwrap()).is_ok());
    // A model of a different assertion set must not be accepted as this query's model.
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(query.root.eq(query.proofs.unused()));
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(matches!(
        query.decode(&solver.get_model().unwrap()),
        Err(SearchError::InvalidModel(_))
    ));
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ReferenceProof {
    Context(Expr<()>),
    And(Vec<ReferenceProof>),
}
fn reference_proofs(goal: &Expr<()>, facts: &[Expr<()>], capacity: usize) -> Vec<ReferenceProof> {
    let mut result = Vec::new();
    if facts.contains(goal) {
        result.push(ReferenceProof::Context(goal.clone()));
    }
    if let RawExpr::Finop(Finop::And, operands) = &goal.raw
        && !operands.is_empty()
        && operands.len() <= capacity
    {
        let mut products = vec![vec![]];
        for operand in operands {
            let choices = reference_proofs(operand, facts, capacity);
            products = products
                .into_iter()
                .flat_map(|prefix| {
                    choices.iter().map(move |child| {
                        let mut p = prefix.clone();
                        p.push(child.clone());
                        p
                    })
                })
                .collect();
        }
        result.extend(products.into_iter().map(ReferenceProof::And));
    }
    result
}
fn reference_search(goal: &Expr<()>, facts: &[Expr<()>], n: usize, capacity: usize) -> bool {
    reference_proofs(goal, facts, capacity)
        .into_iter()
        .any(|root| {
            let mut queue = Vec::new();
            if matches!(root, ReferenceProof::And(_)) {
                queue.push(root);
            }
            let mut cursor = 0;
            while cursor < queue.len() {
                let ReferenceProof::And(children) = queue[cursor].clone() else {
                    unreachable!()
                };
                for child in children {
                    if matches!(child, ReferenceProof::And(_)) && !queue.contains(&child) {
                        queue.push(child);
                    }
                }
                cursor += 1;
            }
            queue.len() <= n
        })
}

#[test]
fn small_generated_queries_match_independent_bfs_and_replay() {
    let pair = and(vec![atom("p"), atom("q")]);
    let contexts = [
        vec![],
        vec![atom("p")],
        vec![atom("p"), atom("q")],
        vec![pair.clone()],
        vec![atom("p"), atom("q"), pair.clone()],
    ];
    let goals = [
        atom("p"),
        atom("q"),
        atom("s"),
        pair.clone(),
        and(vec![atom("q"), atom("p")]),
        and(vec![atom("p"), atom("p")]),
        and(vec![atom("p"), pair]),
        and(vec![atom("p"), atom("q"), atom("p")]),
    ];
    let mut successes = 0;
    let mut failures = 0;
    for facts in contexts {
        let c = context(&facts);
        let before = c.store_counts();
        for goal in &goals {
            for n in 0..=2 {
                for capacity in 1..=3 {
                    let expected = reference_search(goal, &facts, n, capacity);
                    match search(&c, goal, n, capacity) {
                        Ok((_, d)) => {
                            assert!(
                                expected,
                                "unexpected proof for {facts:?}, {goal:?}, {n}, {capacity}"
                            );
                            replay(&c, &d.proof, goal);
                            successes += 1;
                        }
                        Err(SearchError::NoProofWithinBounds(_)) => {
                            assert!(
                                !expected,
                                "missing proof for {facts:?}, {goal:?}, {n}, {capacity}"
                            );
                            failures += 1;
                        }
                        Err(e) => panic!("unexpected search error: {e}"),
                    }
                }
            }
        }
        assert_eq!(c.store_counts(), before);
    }
    assert!(successes > 0 && failures > 0);
}

#[test]
fn backend_proof_snapshots() {
    let p = atom("p");
    let q = atom("q");
    let r = atom("r");
    let pair = and(vec![p.clone(), q.clone()]);
    let flat = crate::from_tex::expr(&ratex_parser::parse(r"p \land q \land r").unwrap()).unwrap();
    let nested = and(vec![p.clone(), and(vec![q.clone(), r.clone()])]);
    let diamond = and(vec![
        and(vec![pair.clone(), r.clone()]),
        and(vec![pair.clone(), atom("s")]),
    ]);
    let cases = [
        ("Contextual reuse", vec![p.clone()], p.clone(), 0, 3),
        (
            "Binary introduction",
            vec![p.clone(), q.clone()],
            pair.clone(),
            1,
            3,
        ),
        (
            "Three-premise introduction",
            vec![p.clone(), q.clone(), r.clone()],
            flat.clone(),
            1,
            3,
        ),
        (
            "Nested introduction: insufficient slots",
            vec![p.clone(), q.clone(), r.clone()],
            nested.clone(),
            1,
            3,
        ),
        (
            "Nested introduction: sufficient slots",
            vec![p.clone(), q.clone(), r.clone()],
            nested,
            2,
            3,
        ),
        (
            "Flat conjunction: capacity two",
            vec![p.clone(), q.clone(), r.clone()],
            flat.clone(),
            4,
            2,
        ),
        (
            "Flat conjunction: capacity three",
            vec![p.clone(), q.clone(), r.clone()],
            flat,
            1,
            3,
        ),
        (
            "Repeated subproof",
            vec![p.clone(), q.clone()],
            and(vec![pair.clone(), pair.clone()]),
            2,
            3,
        ),
        (
            "Shared descendant: insufficient distinct-node budget",
            vec![p.clone(), q.clone(), r.clone(), atom("s")],
            diamond.clone(),
            3,
            3,
        ),
        (
            "Shared descendant: four distinct nodes",
            vec![p.clone(), q, r, atom("s")],
            diamond,
            4,
            3,
        ),
        (
            "Missing contextual premise",
            vec![p.clone()],
            pair.clone(),
            2,
            3,
        ),
        ("Elimination is not an available rule", vec![pair], p, 2, 3),
    ];
    let mut sections = Vec::new();
    for (name, facts, goal, n, capacity) in cases {
        let c = context(&facts);
        let outcome = match search(&c, &goal, n, capacity) {
            Ok((_, d)) => {
                replay(&c, &d.proof, &goal);
                format!("Found proof.\n\n{}", d.proof.details(&goal))
            }
            Err(e @ SearchError::NoProofWithinBounds(_)) => e.to_string(),
            Err(e) => panic!("{e}"),
        };
        sections.push(format!("# {name}\n\nContext:\n\n{}\n\nGoal: ${}$\n\nLimits: {n} rule slots, {capacity} premises per inference.\n\n{outcome}", facts.iter().map(|e|format!("- ${}$",e.as_latex())).collect::<Vec<_>>().join("\n"),goal.as_latex()));
    }
    expect_test::expect_file!["../snapshots/smt_backend.md"]
        .assert_eq(&(sections.join("\n\n") + "\n"));
}

#[test]
fn frozen_comparison_chain_leaves_keep_literal_and_resolved_evidence() {
    let mut c = context(&[]);
    c.declare_parameter(Variable::new("x"), TypeExpr::Real);
    let parse = |tex| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let chain = parse("0<x<2");
    let checked = c.check(&chain).unwrap();
    c.assume(checked, vec![]).unwrap();
    let (_, literal) = search(&c, &chain, 0, 3).unwrap();
    assert!(matches!(
        literal.proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Literal,
            ..
        }
    ));
    let target = and(vec![parse("0<x"), parse("x<2")]);
    let (_, resolved) = search(&c, &target, 0, 3).unwrap();
    assert!(matches!(
        resolved.proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Resolved,
            ..
        }
    ));
    assert_eq!(resolved.proof.supporting_facts(), vec![chain]);
}

#[test]
fn inferred_dependencies_reuse_existing_witness_discharge_and_scope_policy() {
    let mut c = context(&[atom("p")]);
    let existential =
        crate::from_tex::expr(&ratex_parser::parse(r"\exists x \in \mathbb{R}, x>0").unwrap())
            .unwrap();
    let checked = c.check(&existential).unwrap();
    c.assume(checked, vec![]).unwrap();
    let mut child = c.clone();
    child.enter_scope();
    struct Checks;
    impl SideConditionChecker for Checks {
        fn check_instantiation(
            &mut self,
            _: &QuantifierSpec,
            _: &BTreeMap<Variable, Expr<()>>,
            _: &BTreeSet<(ImplicitDimension, ImplicitDimension)>,
            _: &[Expr<()>],
        ) -> SideConditionResult {
            SideConditionResult::Valid
        }
    }
    let witness = crate::from_tex::expr(&ratex_parser::parse("a>0").unwrap()).unwrap();
    let NaturalDeductionResult::Established {
        conclusion,
        mut derivations,
    } = follows_from_natural_deduction(&child, &witness, &SurfaceInterpreter, &mut Checks)
    else {
        panic!()
    };
    child
        .open_witness(conclusion, vec![], derivations.remove(0))
        .unwrap();
    let (_, d) = search(&child, &and(vec![atom("p"), witness]), 1, 3).unwrap();
    assert!(d.required_variables.contains(&Variable::new("a")));
    // Its witness parameter is still local; no export is made by finding a proof.
    assert_eq!(c.facts().len(), 2);
    let closed = child.check(&and(vec![atom("p"), atom("p")])).unwrap();
    // A legitimate externally checked p ∧ p is conservatively dependent on
    // every active assumption. Acceptance performs the existing witness discharge.
    child.record_external(closed, vec![]).unwrap();
    let external = child
        .facts()
        .iter()
        .find(|f| f.formula().meaning() == and(vec![atom("p"), atom("p")]))
        .unwrap();
    assert!(
        external
            .derivations()
            .any(|d| !d.witness_discharges.is_empty())
    );
    let goal = and(vec![and(vec![atom("p"), atom("p")]), atom("p")]);
    let (checked, d) = search(&child, &goal, 1, 3).unwrap();
    assert!(!d.assumptions.contains(&child.witnesses[0].assumption));
    assert!(!d.required_variables.contains(&Variable::new("a")));
    child.record(checked, vec![], vec![d]).unwrap();
    assert!(!child.export_delta(&c).unwrap().is_empty());
}

#[test]
fn saved_binder_scopes_survive_later_same_named_parameter_declarations() {
    let mut c = context(&[]);
    let formula =
        crate::from_tex::expr(&ratex_parser::parse(r"\sum_{i=1}^{2} i = 3").unwrap()).unwrap();
    let checked = c.check(&formula).unwrap();
    c.assume(checked, vec![]).unwrap();
    c.declare_parameter(Variable::new("i"), TypeExpr::Nat);
    let mut index = Variable::new("i");
    index.annotations.push(crate::Annotation::Prime);
    let renamed = Expr::new(RawExpr::CmpChain(CmpChain {
        start: Expr::new(RawExpr::Seqop(
            crate::SeqOp::Sum,
            crate::Range {
                index_variable: index.clone(),
                from: Expr::new(RawExpr::NatLiteral(1)),
                to: Expr::new(RawExpr::NatLiteral(2)),
            },
            Expr::new(RawExpr::Variable(index)),
        )),
        assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(3)))],
    }));
    let (_, d) = search(&c, &renamed, 0, 3).unwrap();
    assert!(matches!(
        d.proof,
        NaturalDeductionProof::Reuse {
            kind: ReuseKind::Resolved,
            ..
        }
    ));
    assert!(!d.required_variables.contains(&Variable::new("i")));
    assert_eq!(d.proof.supporting_facts(), vec![formula]);
}
