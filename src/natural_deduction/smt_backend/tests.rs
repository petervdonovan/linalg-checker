use super::*;
use crate::{Cmp, CmpChain, Monop};

fn atom(name: &str) -> Expr<()> {
    Expr::new(RawExpr::Variable(Variable::new(name)))
}
fn or(xs: Vec<Expr<()>>) -> Expr<()> {
    Expr::new(RawExpr::Finop(Finop::Or, xs))
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
        max_finop_arity: 3,
        max_root_dependencies: None,
        timeout_ms: None,
    }
}
fn search(
    c: &ProofContext,
    goal: &Expr<()>,
    n: usize,
    capacity: usize,
) -> Result<(CheckedFormula, Derivation), SearchError> {
    find_proof(
        c,
        goal,
        &SurfaceInterpreter,
        limits(n, capacity),
        &Timings::default(),
    )
}
fn replay_input(c: &ProofContext, input: &ProofInput) -> (Expr<()>, BTreeSet<AssumptionId>) {
    match input {
        ProofInput::Context(p) => {
            let fact = c
                .facts()
                .iter()
                .find(|f| f.id() == p.fact)
                .expect("visible source");
            let d = fact
                .derivations()
                .find(|d| d.id == p.derivation)
                .expect("visible derivation");
            assert_eq!(p.expression, *fact.formula().written());
            assert_eq!(p.conjunct, 0);
            assert_eq!(p.alternative, None);
            (fact.formula().meaning(), d.assumptions.clone())
        }
        ProofInput::Local { conclusion, proof } => {
            (conclusion.clone(), replay(c, proof, conclusion))
        }
    }
}
fn replay(
    c: &ProofContext,
    proof: &NaturalDeductionProof,
    conclusion: &Expr<()>,
) -> BTreeSet<AssumptionId> {
    match proof {
        NaturalDeductionProof::Assumption { assumption } => BTreeSet::from([*assumption]),
        NaturalDeductionProof::Reuse { premise, .. } => {
            let (p, set) = replay_input(c, premise);
            assert_eq!(p, *conclusion);
            set
        }
        NaturalDeductionProof::ConjunctionIntroduction { premises } => {
            assert!(!premises.is_empty());
            let mut formulas = Vec::new();
            let mut all = BTreeSet::new();
            for p in premises {
                let (formula, set) = replay_input(c, p);
                formulas.push(formula);
                all.extend(set);
            }
            assert_eq!(and(formulas), *conclusion);
            all
        }
        NaturalDeductionProof::ConjunctionElimination { premise, operand } => {
            let (formula, set) = replay_input(c, premise);
            let RawExpr::Finop(Finop::And, values) = &formula.raw else {
                panic!()
            };
            assert_eq!(values[*operand], *conclusion);
            set
        }
        NaturalDeductionProof::DisjunctionIntroduction { premise, operand } => {
            let (formula, set) = replay_input(c, premise);
            let RawExpr::Finop(Finop::Or, values) = &conclusion.raw else {
                panic!()
            };
            assert_eq!(values[*operand], formula);
            set
        }
        NaturalDeductionProof::DisjunctionElimination { disjunction, cases } => {
            let (formula, mut all) = replay_input(c, disjunction);
            let RawExpr::Finop(Finop::Or, operands) = &formula.raw else {
                panic!()
            };
            assert!(!operands.is_empty());
            assert_eq!(operands.len(), cases.len());
            for (case, operand) in cases.iter().zip(operands.iter().cloned()) {
                let (formula, mut set) = replay_input(c, &case.premise);
                assert_eq!(formula, *conclusion);
                assert_eq!(case.discharged.len(), case.discharged_formulas.len());
                for id in &case.discharged {
                    assert_eq!(case.discharged_formulas[id], operand);
                    assert!(set.remove(id));
                }
                all.extend(set);
            }
            all
        }
        NaturalDeductionProof::ImplicationElimination {
            implication,
            antecedent,
        } => {
            let (formula, mut deps) = replay_input(c, implication);
            let (argument, argument_deps) = replay_input(c, antecedent);
            let RawExpr::LogicChain(chain) = &formula.raw else {
                panic!()
            };
            assert_eq!(chain.start, argument);
            assert_eq!(chain.assertions, vec![(Logic::Imp, conclusion.clone())]);
            deps.extend(argument_deps);
            deps
        }
        NaturalDeductionProof::ImplicationIntroduction {
            premise,
            discharged,
            discharged_formulas,
        } => {
            let RawExpr::LogicChain(chain) = &conclusion.raw else {
                panic!()
            };
            let [(Logic::Imp, body)] = chain.assertions.as_slice() else {
                panic!()
            };
            let (formula, mut set) = replay_input(c, premise);
            assert_eq!(formula, *body);
            for a in discharged {
                assert_eq!(discharged_formulas[a], chain.start);
                assert!(set.remove(a));
            }
            set
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
fn source_selection_preserves_whole_fact_identity_and_bindings() {
    let c = context(&[atom("p"), atom("p")]);
    let (_, d) = search(&c, &atom("p"), 0, 3).unwrap();
    let selected = c.derivation(d.proof.leaves()[0].derivation).unwrap();
    assert_eq!(d.assumptions, selected.assumptions);
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
fn bounds_preserve_nary_structure_and_allow_explicit_elimination() {
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
        search(&c, &atom("p"), 3, 3).unwrap().1.proof,
        NaturalDeductionProof::ConjunctionElimination { .. }
    ));
    // A whole contextual formula needs no construction capacity.
    assert!(search(&c, &and(vec![atom("p"), atom("q")]), 0, 0).is_ok());
}

#[test]
fn options_analysis_encoding_and_solver_failures_are_distinct() {
    let c = context(&[]);
    let timings = Timings::new("Invalid options", 0);
    assert!(matches!(
        find_proof(
            &c,
            &atom("p"),
            &SurfaceInterpreter,
            SearchLimits {
                timeout_ms: Some(0),
                ..limits(1, 3)
            },
            &timings,
        ),
        Err(SearchError::InvalidOptions(_))
    ));
    let measured = timings.times();
    assert!(measured.contains_key("total_ms"));
    assert!(measured.contains_key("query_ms"));
    assert!(!measured.contains_key("z3_dt_ms"));
    assert!(!measured.contains_key("decode_ms"));
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
    assert_eq!(query.solver.check(), SatResult::Sat);
    let valid_model = query.solver.get_model().unwrap();
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&query.proofs.unused(), 1),
        Err(SearchError::InvalidModel(_))
    ));
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&query.proofs.constant("unassigned"), 1),
        Err(SearchError::InvalidModel(_))
    ));
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&query.expressions.constant("not_a_proof"), 1),
        Err(SearchError::InvalidModel(_))
    ));
    let mut other = ExprDatatype::new("decode_foreign_expr");
    let other_proof = ProofDatatype::new("decode_foreign_proof", &other);
    let foreign = other_proof
        .established(&other.encode(&atom("p")).unwrap(), 0, &other)
        .unwrap();
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&foreign, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let r = query.expressions.encode(&atom("r")).unwrap();
    let unknown = query
        .proofs
        .established(&r, 999, &query.expressions)
        .unwrap();
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&unknown, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let conclusion_p = query
        .proofs
        .conclusion(&query.leaves[0].value)
        .unwrap()
        .simplify();
    assert!(matches!(
        Decoder::new(&query, &valid_model).unwrap().decode_value(
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
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&invalid, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let empty = query
        .proofs
        .inference(&query.target, ProofRule::AndIntroduction, &[])
        .unwrap();
    assert!(matches!(
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&empty, 1),
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
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&unused, 1),
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
        Decoder::new(&query, &valid_model)
            .unwrap()
            .decode_value(&oversized, 1),
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
    Leaf {
        formula: Expr<()>,
        source: usize,
    },
    And(Vec<ReferenceProof>),
    Or {
        conclusion: Expr<()>,
        premise: Box<ReferenceProof>,
    },
    Elim {
        premise: Box<ReferenceProof>,
        operand: usize,
    },
    Cases {
        conclusion: Expr<()>,
        disjunction: Box<ReferenceProof>,
        cases: Vec<ReferenceProof>,
    },
    Apply {
        implication: Box<ReferenceProof>,
        antecedent: Box<ReferenceProof>,
    },
    Imp {
        antecedent: Expr<()>,
        body: Box<ReferenceProof>,
    },
}
fn reference_proofs(
    goal: &Expr<()>,
    assumptions: &[Expr<()>],
    capacity: usize,
    depth: usize,
) -> Vec<ReferenceProof> {
    let mut result = assumptions
        .iter()
        .enumerate()
        .filter(|(_, a)| *a == goal)
        .map(|(source, formula)| ReferenceProof::Leaf {
            formula: formula.clone(),
            source,
        })
        .collect::<Vec<_>>();
    if depth == 0 {
        return result;
    }
    // Normal proofs need elimination chains from assumptions, not introduction-
    // elimination detours. Keep this finite oracle restriction out of production.
    fn projections(
        formula: &Expr<()>,
        proof: ReferenceProof,
        goal: &Expr<()>,
        result: &mut Vec<ReferenceProof>,
    ) {
        if let RawExpr::Finop(Finop::And, operands) = &formula.raw {
            for (operand, value) in operands.iter().enumerate() {
                let projected = ReferenceProof::Elim {
                    premise: Box::new(proof.clone()),
                    operand,
                };
                if value == goal {
                    result.push(projected.clone());
                }
                projections(value, projected, goal, result);
            }
        }
    }
    if capacity > 0 {
        for (source, formula) in assumptions.iter().enumerate() {
            projections(
                formula,
                ReferenceProof::Leaf {
                    formula: formula.clone(),
                    source,
                },
                goal,
                &mut result,
            );
        }
    }
    if let RawExpr::Finop(Finop::And, operands) = &goal.raw
        && !operands.is_empty()
        && operands.len() <= capacity
    {
        let mut products = vec![vec![]];
        for operand in operands {
            let choices = reference_proofs(operand, assumptions, capacity, depth - 1);
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
    if capacity > 0
        && let RawExpr::Finop(Finop::Or, operands) = &goal.raw
    {
        for (index, operand) in operands.iter().enumerate() {
            // The wire proof stores the premise and complete conclusion, not a
            // positional choice. Duplicate disjuncts cannot create distinct nodes.
            if operands[..index].contains(operand) {
                continue;
            }
            result.extend(
                reference_proofs(operand, assumptions, capacity, depth - 1)
                    .into_iter()
                    .map(|premise| ReferenceProof::Or {
                        conclusion: goal.clone(),
                        premise: Box::new(premise),
                    }),
            );
        }
    }
    if capacity > 0
        && let RawExpr::LogicChain(chain) = &goal.raw
        && let [(Logic::Imp, body)] = chain.assertions.as_slice()
    {
        result.extend(
            reference_proofs(body, assumptions, capacity, depth - 1)
                .into_iter()
                .map(|p| ReferenceProof::Imp {
                    antecedent: chain.start.clone(),
                    body: Box::new(p),
                }),
        );
    }
    if capacity >= 2 {
        fn implications(formula: &Expr<()>, output: &mut Vec<Expr<()>>) {
            match &formula.raw {
                RawExpr::Finop(Finop::And | Finop::Or, operands) => {
                    for operand in operands {
                        implications(operand, output);
                    }
                }
                RawExpr::LogicChain(chain) => {
                    if let [(Logic::Imp, body)] = chain.assertions.as_slice() {
                        if !output.contains(formula) {
                            output.push(formula.clone());
                        }
                        implications(&chain.start, output);
                        implications(body, output);
                    }
                }
                _ => (),
            }
        }
        let mut candidates = Vec::new();
        for formula in assumptions.iter().chain(std::iter::once(goal)) {
            implications(formula, &mut candidates);
        }
        for candidate in candidates {
            let RawExpr::LogicChain(chain) = &candidate.raw else {
                unreachable!()
            };
            let [(Logic::Imp, body)] = chain.assertions.as_slice() else {
                unreachable!()
            };
            if body != goal {
                continue;
            }
            let sources = reference_proofs(&candidate, assumptions, capacity, depth - 1);
            let arguments = reference_proofs(&chain.start, assumptions, capacity, depth - 1);
            for source in sources {
                for argument in &arguments {
                    result.push(ReferenceProof::Apply {
                        implication: Box::new(source.clone()),
                        antecedent: Box::new(argument.clone()),
                    });
                }
            }
        }
    }
    // Normal case-analysis sources are disjunction subformulas of assumptions.
    // Recursive generation is depth bounded, then the BFS check counts shared nodes.
    fn disjunctions(formula: &Expr<()>, output: &mut Vec<Expr<()>>) {
        if let RawExpr::Finop(Finop::And | Finop::Or, operands) = &formula.raw {
            if matches!(&formula.raw, RawExpr::Finop(Finop::Or, _))
                && !operands.is_empty()
                && !output.contains(formula)
            {
                output.push(formula.clone());
            }
            for operand in operands {
                disjunctions(operand, output);
            }
        }
    }
    let mut sources = Vec::new();
    for formula in assumptions {
        disjunctions(formula, &mut sources);
    }
    for source in sources {
        let RawExpr::Finop(Finop::Or, operands) = &source.raw else {
            unreachable!()
        };
        if operands.len() + 1 > capacity {
            continue;
        }
        let source_proofs = reference_proofs(&source, assumptions, capacity, depth - 1);
        if source_proofs.is_empty() {
            continue;
        }
        // All branch conclusions are equal, but evidence/dependencies may differ.
        let choices = reference_proofs(goal, assumptions, capacity, depth - 1);
        let mut products = vec![vec![]];
        for _ in operands {
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
        for disjunction in source_proofs {
            for cases in &products {
                result.push(ReferenceProof::Cases {
                    conclusion: goal.clone(),
                    disjunction: Box::new(disjunction.clone()),
                    cases: cases.clone(),
                });
            }
        }
    }
    result
}
fn reference_formula(proof: &ReferenceProof) -> Expr<()> {
    match proof {
        ReferenceProof::Leaf { formula, .. }
        | ReferenceProof::Or {
            conclusion: formula,
            ..
        }
        | ReferenceProof::Cases {
            conclusion: formula,
            ..
        } => formula.clone(),
        ReferenceProof::And(children) => and(children.iter().map(reference_formula).collect()),
        ReferenceProof::Elim { premise, operand } => {
            let RawExpr::Finop(Finop::And, values) = &reference_formula(premise).raw else {
                panic!()
            };
            values[*operand].clone()
        }
        ReferenceProof::Apply { implication, .. } => {
            let RawExpr::LogicChain(chain) = &reference_formula(implication).raw else {
                panic!()
            };
            chain.assertions[0].1.clone()
        }
        ReferenceProof::Imp { antecedent, body } => {
            implication(antecedent.clone(), reference_formula(body))
        }
    }
}
fn reference_search(
    goal: &Expr<()>,
    facts: &[Expr<()>],
    n: usize,
    capacity: usize,
    bound: Option<usize>,
) -> bool {
    // Normal proofs in these finite fixtures have the subformula property.
    // One temporary identity per distinct antecedent is enough: merging equal
    // temporary formulas cannot increase proof size or change ambient support.
    fn antecedents(goal: &Expr<()>, output: &mut Vec<Expr<()>>) {
        match &goal.raw {
            RawExpr::Finop(Finop::And | Finop::Or, values) => {
                for v in values {
                    if matches!(&goal.raw, RawExpr::Finop(Finop::Or, _)) && !output.contains(v) {
                        output.push(v.clone());
                    }
                    antecedents(v, output)
                }
            }
            RawExpr::LogicChain(chain) => {
                if let [(Logic::Imp, body)] = chain.assertions.as_slice() {
                    if !output.contains(&chain.start) {
                        output.push(chain.start.clone());
                    }
                    antecedents(&chain.start, output);
                    antecedents(body, output);
                }
            }
            _ => (),
        }
    }
    fn dependencies(proof: &ReferenceProof, assumptions: &[Expr<()>]) -> BTreeSet<usize> {
        match proof {
            ReferenceProof::Leaf { source, .. } => BTreeSet::from([*source]),
            ReferenceProof::Elim { premise, .. } | ReferenceProof::Or { premise, .. } => {
                dependencies(premise, assumptions)
            }
            ReferenceProof::And(children) => children
                .iter()
                .flat_map(|c| dependencies(c, assumptions))
                .collect(),
            ReferenceProof::Cases {
                disjunction, cases, ..
            } => {
                let RawExpr::Finop(Finop::Or, operands) = &reference_formula(disjunction).raw
                else {
                    panic!()
                };
                let mut all = dependencies(disjunction, assumptions);
                for (case, operand) in cases.iter().zip(operands.iter().cloned()) {
                    all.extend(
                        dependencies(case, assumptions)
                            .into_iter()
                            .filter(|a| assumptions[*a] != operand),
                    );
                }
                all
            }
            ReferenceProof::Apply {
                implication,
                antecedent,
            } => {
                let mut deps = dependencies(implication, assumptions);
                deps.extend(dependencies(antecedent, assumptions));
                deps
            }
            ReferenceProof::Imp { antecedent, body } => dependencies(body, assumptions)
                .into_iter()
                .filter(|a| assumptions[*a] != *antecedent)
                .collect(),
        }
    }
    fn children(proof: &ReferenceProof) -> Vec<&ReferenceProof> {
        match proof {
            ReferenceProof::Leaf { .. } => vec![],
            ReferenceProof::And(c) => c.iter().collect(),
            ReferenceProof::Elim { premise, .. } | ReferenceProof::Or { premise, .. } => {
                vec![premise]
            }
            ReferenceProof::Cases {
                disjunction, cases, ..
            } => std::iter::once(disjunction.as_ref()).chain(cases).collect(),
            ReferenceProof::Imp { body, .. } => vec![body],
            ReferenceProof::Apply {
                implication,
                antecedent,
            } => vec![implication, antecedent],
        }
    }
    let mut temporary = Vec::new();
    antecedents(goal, &mut temporary);
    for fact in facts {
        antecedents(fact, &mut temporary);
    }
    let all = facts.iter().chain(&temporary).cloned().collect::<Vec<_>>();
    reference_proofs(goal, &all, capacity, n)
        .into_iter()
        .any(|root| {
            let deps = dependencies(&root, &all);
            if deps.iter().any(|a| *a >= facts.len()) || bound.is_some_and(|b| deps.len() > b) {
                return false;
            }
            let mut queue = Vec::new();
            if !matches!(root, ReferenceProof::Leaf { .. }) {
                queue.push(root);
            }
            let mut cursor = 0;
            while cursor < queue.len() {
                let next = children(&queue[cursor])
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                for child in next {
                    if !matches!(child, ReferenceProof::Leaf { .. }) && !queue.contains(&child) {
                        queue.push(child);
                    }
                }
                cursor += 1;
            }
            queue.len() <= n
        })
}

#[test]
fn small_generated_queries_match_independent_bfs_dependencies_and_replay() {
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
        implication(atom("p"), atom("p")),
        implication(atom("p"), atom("q")),
        implication(atom("p"), and(vec![atom("p"), atom("p")])),
        implication(atom("p"), implication(atom("q"), atom("p"))),
        and(vec![implication(atom("p"), atom("p")), atom("p")]),
        or(vec![atom("p"), atom("q")]),
        or(vec![atom("p"), atom("p")]),
        or(vec![atom("p"), or(vec![atom("q"), atom("r")])]),
        implication(atom("p"), or(vec![atom("p"), atom("q")])),
        or(vec![implication(atom("p"), atom("p")), atom("q")]),
    ];
    let mut successes = 0;
    let mut failures = 0;
    for facts in contexts {
        let c = context(&facts);
        let before = c.store_counts();
        for goal in &goals {
            for n in 0..=2 {
                for capacity in [1, 3] {
                    for bound in [None, Some(0), Some(1)] {
                        let expected = reference_search(goal, &facts, n, capacity, bound);
                        match find_proof(
                            &c,
                            goal,
                            &SurfaceInterpreter,
                            SearchLimits {
                                max_root_dependencies: bound,
                                ..limits(n, capacity)
                            },
                            &Timings::default(),
                        ) {
                            Ok((_, d)) => {
                                assert!(
                                    expected,
                                    "unexpected proof for {facts:?}, {goal:?}, {n}, {capacity}, {bound:?}"
                                );
                                assert_eq!(replay(&c, &d.proof, goal), d.assumptions);
                                assert!(bound.is_none_or(|b| d.assumptions.len() <= b));
                                successes += 1;
                            }
                            Err(SearchError::NoProofWithinBounds(_)) => {
                                assert!(
                                    !expected,
                                    "missing proof for {facts:?}, {goal:?}, {n}, {capacity}, {bound:?}"
                                );
                                failures += 1;
                            }
                            Err(e) => panic!("unexpected search error: {e}"),
                        }
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
        ("Contextual reuse", vec![p.clone()], p.clone(), 0, 3, None),
        (
            "Binary introduction",
            vec![p.clone(), q.clone()],
            pair.clone(),
            1,
            3,
            None,
        ),
        (
            "Three-premise introduction",
            vec![p.clone(), q.clone(), r.clone()],
            flat.clone(),
            1,
            3,
            None,
        ),
        (
            "Nested introduction: insufficient slots",
            vec![p.clone(), q.clone(), r.clone()],
            nested.clone(),
            1,
            3,
            None,
        ),
        (
            "Nested introduction: sufficient slots",
            vec![p.clone(), q.clone(), r.clone()],
            nested,
            2,
            3,
            None,
        ),
        (
            "Flat conjunction: capacity two",
            vec![p.clone(), q.clone(), r.clone()],
            flat.clone(),
            4,
            2,
            None,
        ),
        (
            "Flat conjunction: capacity three",
            vec![p.clone(), q.clone(), r.clone()],
            flat,
            1,
            3,
            None,
        ),
        (
            "Repeated subproof",
            vec![p.clone(), q.clone()],
            and(vec![pair.clone(), pair.clone()]),
            2,
            3,
            None,
        ),
        (
            "Shared descendant: insufficient distinct-node budget",
            vec![p.clone(), q.clone(), r.clone(), atom("s")],
            diamond.clone(),
            3,
            3,
            None,
        ),
        (
            "Shared descendant: four distinct nodes",
            vec![p.clone(), q.clone(), r, atom("s")],
            diamond,
            4,
            3,
            None,
        ),
        (
            "Missing contextual premise",
            vec![p.clone()],
            pair.clone(),
            2,
            3,
            None,
        ),
        ("Conjunction elimination", vec![pair], p.clone(), 2, 3, None),
        (
            "Third conjunct of an n-ary assumption",
            vec![and(vec![p.clone(), q.clone(), atom("r")])],
            atom("r"),
            1,
            1,
            Some(1),
        ),
        (
            "Nested conjunction elimination",
            vec![and(vec![p.clone(), and(vec![q.clone(), atom("r")])])],
            atom("r"),
            2,
            1,
            Some(1),
        ),
        (
            "Projection under implication introduction",
            vec![],
            implication(and(vec![p.clone(), q.clone()]), q.clone()),
            2,
            1,
            Some(0),
        ),
        (
            "Temporary assumption identity",
            vec![],
            implication(p.clone(), p.clone()),
            1,
            3,
            Some(0),
        ),
        (
            "One temporary assumption used twice",
            vec![],
            implication(p.clone(), and(vec![p.clone(), p.clone()])),
            2,
            3,
            Some(0),
        ),
        (
            "Vacuous inner discharge",
            vec![],
            implication(p.clone(), implication(q.clone(), p.clone())),
            2,
            3,
            Some(0),
        ),
        (
            "Nested discharges",
            vec![],
            implication(
                p.clone(),
                implication(q.clone(), and(vec![p.clone(), q.clone()])),
            ),
            3,
            3,
            Some(0),
        ),
        (
            "Independent closed branches",
            vec![],
            and(vec![
                implication(p.clone(), p.clone()),
                implication(q.clone(), q.clone()),
            ]),
            3,
            3,
            Some(0),
        ),
        (
            "Temporary assumption cannot escape a sibling",
            vec![],
            and(vec![implication(p.clone(), p.clone()), p.clone()]),
            3,
            3,
            None,
        ),
        (
            "Remaining ambient dependency",
            vec![q.clone()],
            implication(p.clone(), and(vec![p.clone(), q.clone()])),
            2,
            3,
            Some(1),
        ),
        (
            "Root dependency bound zero",
            vec![q.clone()],
            implication(p.clone(), and(vec![p.clone(), q])),
            2,
            3,
            Some(0),
        ),
        (
            "One ambient assumption used twice",
            vec![p.clone()],
            and(vec![p.clone(), p]),
            1,
            3,
            Some(1),
        ),
    ];
    let disjunction_cases = [
        (
            "First disjunct",
            vec![atom("p")],
            or(vec![atom("p"), atom("q"), atom("r")]),
            1,
            1,
            Some(1),
        ),
        (
            "Middle disjunct",
            vec![atom("q")],
            or(vec![atom("p"), atom("q"), atom("r")]),
            1,
            1,
            Some(1),
        ),
        (
            "Last disjunct",
            vec![atom("r")],
            or(vec![atom("p"), atom("q"), atom("r")]),
            1,
            1,
            Some(1),
        ),
        (
            "Nested disjunction introduction",
            vec![atom("q")],
            or(vec![atom("p"), or(vec![atom("q"), atom("r")])]),
            2,
            1,
            Some(1),
        ),
        (
            "Disjunction under implication introduction",
            vec![],
            implication(atom("p"), or(vec![atom("p"), atom("q")])),
            2,
            1,
            Some(0),
        ),
        (
            "Closed implication as a disjunct",
            vec![],
            or(vec![implication(atom("p"), atom("p")), atom("q")]),
            2,
            1,
            Some(0),
        ),
        (
            "Disjunction has no established operand",
            vec![],
            or(vec![atom("p"), atom("q")]),
            2,
            1,
            None,
        ),
        (
            "Disjunction does not eliminate",
            vec![or(vec![atom("p"), atom("q")])],
            atom("p"),
            2,
            1,
            None,
        ),
    ];
    let elimination_cases = [
        (
            "Binary disjunction case analysis",
            vec![or(vec![atom("p"), atom("q")])],
            or(vec![atom("q"), atom("p")]),
            3,
            3,
            None,
        ),
        (
            "Ternary disjunction case analysis",
            vec![or(vec![atom("p"), atom("q"), atom("r")])],
            or(vec![atom("r"), atom("q"), atom("p")]),
            4,
            4,
            None,
        ),
        (
            "Nested case analysis",
            vec![or(vec![atom("p"), or(vec![atom("q"), atom("p")])])],
            or(vec![atom("p"), atom("q")]),
            4,
            3,
            None,
        ),
        (
            "Shared case proof",
            vec![or(vec![atom("p"), atom("p")])],
            atom("p"),
            1,
            3,
            None,
        ),
        (
            "Vacuous case discharge",
            vec![or(vec![atom("p"), atom("q")]), atom("r")],
            atom("r"),
            1,
            3,
            None,
        ),
        (
            "Case analysis retains source dependencies",
            vec![or(vec![atom("p"), atom("p")])],
            atom("p"),
            1,
            3,
            Some(0),
        ),
    ];
    let application_cases = [
        (
            "Implication elimination",
            vec![implication(atom("p"), atom("q")), atom("p")],
            atom("q"),
            1,
            2,
            None,
        ),
        (
            "Chained implication elimination",
            vec![
                implication(atom("p"), atom("q")),
                implication(atom("q"), atom("r")),
                atom("p"),
            ],
            atom("r"),
            2,
            2,
            None,
        ),
        (
            "Implication elimination under introduction",
            vec![implication(atom("p"), atom("q"))],
            implication(and(vec![atom("p"), atom("r")]), atom("q")),
            3,
            2,
            Some(1),
        ),
        (
            "Closed modus ponens",
            vec![],
            implication(
                and(vec![implication(atom("p"), atom("q")), atom("p")]),
                atom("q"),
            ),
            4,
            2,
            Some(0),
        ),
        (
            "Implication elimination blocked by dependency bound",
            vec![implication(atom("p"), atom("q")), atom("p")],
            atom("q"),
            1,
            2,
            Some(1),
        ),
    ];
    let mut sections = Vec::new();
    let mut records = Vec::new();
    for (name, facts, goal, n, capacity, bound) in cases
        .into_iter()
        .chain(disjunction_cases)
        .chain(elimination_cases)
        .chain(application_cases)
    {
        let c = context(&facts);
        let timing = Timings::new(name, 0);
        let search_limits = SearchLimits {
            max_root_dependencies: bound,
            ..limits(n, capacity)
        };
        let max_finop_arity = search_limits.max_finop_arity;
        // Force representative vacuous and shared branches rather than letting
        // the solver choose contextual reuse or separate equal-formula leaves.
        let result = if matches!(name, "Vacuous case discharge" | "Shared case proof") {
            let _total = timing.scope("total_ms");
            let query = {
                let _build = timing.scope("query_ms");
                let query = Query::new(&c, &goal, &SurfaceInterpreter, search_limits).unwrap();
                let r = if name == "Shared case proof" {
                    temporary_leaf(&query, 0)
                } else {
                    query.leaves[1].value.clone()
                };
                let forced = query
                    .proofs
                    .inference(
                        &query.target,
                        ProofRule::OrElimination,
                        &[query.leaves[0].value.clone(), r.clone(), r],
                    )
                    .unwrap();
                query.solver.assert(query.root.eq(forced));
                query
            };
            assert_eq!(timing.check(&query.solver, "z3_dt_ms"), SatResult::Sat);
            let _decode = timing.scope("decode_ms");
            let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
            Ok((query.checked, d))
        } else {
            find_proof(&c, &goal, &SurfaceInterpreter, search_limits, &timing)
        };
        records.push(timing);
        let outcome = match result {
            Ok((_, d)) => {
                assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
                let open = if d.assumptions.is_empty() {
                    "none".to_owned()
                } else {
                    d.assumptions
                        .iter()
                        .map(|a| format!("${}$", c.assumptions[a].expression.as_latex()))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                format!(
                    "Found proof.\n\nRemaining assumptions ({}): {open}.\n\n{}",
                    d.assumptions.len(),
                    d.proof.details(&goal)
                )
            }
            Err(e @ SearchError::NoProofWithinBounds(_)) => e.to_string(),
            Err(e) => panic!("{e}"),
        };
        let bound = bound
            .map(|b| b.to_string())
            .unwrap_or_else(|| "unbounded".into());
        sections.push(format!("# {name}\n\nContext:\n\n{}\n\nGoal: ${}$\n\nLimits: {n} rule slots, {capacity} premises per inference, finop arity {max_finop_arity}, {bound} root dependencies.\n\n{outcome}",if facts.is_empty(){"(empty)".to_owned()}else{facts.iter().map(|e|format!("- ${}$",e.as_latex())).collect::<Vec<_>>().join("\n")},goal.as_latex()));
    }
    let csv = crate::timing::to_csv(records).expect("failed to serialize SMT backend timings");
    std::fs::write(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/natural_deduction/snapshots/smt_backend.timing.csv"),
        csv,
    )
    .expect("failed to write SMT backend timings");
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

fn implication(p: Expr<()>, q: Expr<()>) -> Expr<()> {
    Expr::new(RawExpr::LogicChain(crate::LogicChain {
        start: p,
        assertions: vec![(Logic::Imp, q)],
    }))
}
fn bounded(
    c: &ProofContext,
    goal: &Expr<()>,
    slots: usize,
    bound: Option<usize>,
) -> Result<(CheckedFormula, Derivation), SearchError> {
    find_proof(
        c,
        goal,
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: bound,
            ..limits(slots, 3)
        },
        &Timings::default(),
    )
}

#[test]
fn implication_introduction_closes_temporary_assumptions_and_records_without_mutation() {
    let mut c = context(&[]);
    for (goal, slots) in [
        (implication(atom("p"), atom("p")), 1),
        (implication(atom("p"), and(vec![atom("p"), atom("p")])), 2),
        (implication(atom("p"), implication(atom("q"), atom("p"))), 2),
        (
            implication(
                atom("p"),
                implication(atom("q"), and(vec![atom("p"), atom("q")])),
            ),
            3,
        ),
        (
            and(vec![
                implication(atom("p"), atom("p")),
                implication(atom("q"), atom("q")),
            ]),
            3,
        ),
    ] {
        let before = c.store_counts();
        let (checked, d) = bounded(&c, &goal, slots, Some(0)).unwrap();
        assert!(d.assumptions.is_empty());
        replay(&c, &d.proof, &goal);
        assert_eq!(c.store_counts(), before);
        let mut accepting = c.clone();
        accepting.record(checked, vec![], vec![d]).unwrap();
    }
    let goal = implication(atom("p"), atom("p"));
    assert!(matches!(
        bounded(&c, &goal, 0, Some(0)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (checked, d) = bounded(&c, &goal, 1, Some(0)).unwrap();
    c.record(checked, vec![], vec![d]).unwrap();
    assert!(bounded(&c, &goal, 0, Some(0)).is_ok());
}

#[test]
fn temporary_dependencies_cannot_escape_through_a_sibling_or_be_assumed_at_root() {
    let c = context(&[]);
    for goal in [
        atom("p"),
        and(vec![implication(atom("p"), atom("p")), atom("p")]),
    ] {
        assert!(matches!(
            bounded(&c, &goal, 4, None),
            Err(SearchError::NoProofWithinBounds(_))
        ));
    }
    // Projecting the temporary conjunction is now an explicit inference before discharge.
    let goal = implication(and(vec![atom("p"), atom("q")]), atom("p"));
    assert!(bounded(&c, &goal, 3, Some(0)).is_ok());
}

#[test]
fn root_cardinality_counts_identities_not_uses_and_enables_source_selection() {
    let c = context(&[atom("p"), atom("q")]);
    let repeated = and(vec![atom("p"), atom("p")]);
    let (_, d) = bounded(&c, &repeated, 1, Some(1)).unwrap();
    assert_eq!(d.assumptions.len(), 1);
    assert!(matches!(
        bounded(&c, &repeated, 1, Some(0)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let pair = and(vec![atom("p"), atom("q")]);
    assert!(matches!(
        bounded(&c, &pair, 1, Some(1)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    for bound in [None, Some(2), Some(99)] {
        assert_eq!(bounded(&c, &pair, 1, bound).unwrap().1.assumptions.len(), 2);
    }
    let mut c = context(&[atom("p"), atom("r")]);
    let p = *c.assumptions.keys().next().unwrap();
    let r = *c.assumptions.keys().next_back().unwrap();
    let q = c.check(&atom("q")).unwrap();
    let mut first = Derivation::new(NaturalDeductionProof::External);
    first.assumptions.insert(r);
    let mut second = Derivation::new(NaturalDeductionProof::External);
    second.assumptions.insert(p);
    c.record(q, vec![], vec![first, second]).unwrap();
    let fact = c
        .facts()
        .iter()
        .find(|f| f.formula().meaning() == atom("q"))
        .unwrap();
    let alternatives = fact.derivations().collect::<Vec<_>>();
    assert_eq!(alternatives.len(), 2);
    let expected = alternatives[1].id;
    let (_, d) = bounded(&c, &implication(atom("p"), atom("q")), 1, Some(0)).unwrap();
    assert!(d.assumptions.is_empty());
    assert_eq!(d.proof.leaves()[0].derivation, expected);
}

#[test]
fn shared_premises_keep_dependencies_on_each_path() {
    let c = context(&[atom("p"), atom("q")]);
    let body = and(vec![atom("p"), atom("q")]);
    let goal = and(vec![
        implication(atom("p"), body.clone()),
        implication(atom("q"), body),
    ]);
    assert!(matches!(
        bounded(&c, &goal, 4, Some(1)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = bounded(&c, &goal, 4, Some(2)).unwrap();
    assert_eq!(d.assumptions.len(), 2);
    replay(&c, &d.proof, &goal);
}

#[test]
fn root_and_slot_bits_are_exact_and_decoder_replays_them() {
    let c = context(&[atom("p"), atom("q"), atom("r")]);
    let goal = and(vec![atom("p"), atom("q")]);
    let query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 3)).unwrap();
    assert_eq!(query.solver.check(), SatResult::Sat);
    for constraint in [
        query.root_dependencies[0].not(),
        query.root_dependencies[2].clone(),
        query.dependencies[0][1].not(),
        query.root_dependencies[3].clone(),
    ] {
        query.solver.push();
        query.solver.assert(constraint);
        assert_eq!(query.solver.check(), SatResult::Unsat);
        query.solver.pop(1);
    }
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    let root = model.eval(&query.root, true).unwrap();
    for extra in [false, true] {
        let tampered = Solver::new_for_logic("QF_DT").unwrap();
        tampered.assert(query.root.eq(&root));
        tampered.assert(query.slots[0].eq(&root));
        for (a, bit) in query.dependencies[0].iter().enumerate() {
            // One case omits p; the other fabricates a dependency on r.
            tampered.assert(bit.eq(Bool::from_bool(if extra { a < 3 } else { a == 1 })));
        }
        assert_eq!(tampered.check(), SatResult::Sat);
        let bad = tampered.get_model().unwrap();
        assert!(matches!(
            Decoder::new(&query, &bad).unwrap().decode_value(&root, 1),
            Err(SearchError::InvalidModel(_))
        ));
        assert!(matches!(
            query.decode(&bad),
            Err(SearchError::InvalidModel(_))
        ));
    }
}

#[test]
fn temporary_formulas_and_contextual_identities_are_checked() {
    let c = context(&[]);
    let goal = implication(atom("p"), atom("p"));
    let mut query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 3)).unwrap();
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    let q = query.expressions.encode(&atom("q")).unwrap();
    let inconsistent = query
        .proofs
        .assumption(&q, AssumptionRef::Temporary(0), &query.expressions)
        .unwrap();
    assert!(matches!(
        Decoder::new(&query, &model)
            .unwrap()
            .decode_value(&inconsistent, 1),
        Err(SearchError::InvalidModel(_))
    ));
    let c = context(&[atom("p"), atom("p")]);
    let query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(0, 3)).unwrap();
    assert_eq!(query.leaves.len(), 2);
    assert_ne!(query.leaves[0].value, query.leaves[1].value);
    for source in &query.leaves {
        query.solver.push();
        query.solver.assert(query.root.eq(&source.value));
        assert_eq!(query.solver.check(), SatResult::Sat);
        let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
        assert_eq!(
            d.proof.leaves()[0].derivation,
            source.premise.as_ref().unwrap().derivation
        );
        assert_eq!(
            d.assumptions,
            c.derivation(d.proof.leaves()[0].derivation)
                .unwrap()
                .assumptions
        );
        query.solver.pop(1);
    }
}

#[test]
fn established_independent_facts_support_zero_dependency_and_vacuous_discharge() {
    let mut c = context(&[]);
    let checked = c.check(&atom("q")).unwrap();
    c.record_external(checked, vec![]).unwrap();
    assert!(
        bounded(&c, &atom("q"), 0, Some(0))
            .unwrap()
            .1
            .assumptions
            .is_empty()
    );
    let (_, d) = bounded(&c, &implication(atom("p"), atom("q")), 1, Some(0)).unwrap();
    assert!(
        matches!(&d.proof,NaturalDeductionProof::ImplicationIntroduction {discharged,..} if discharged.is_empty())
    );
    let query = Query::new(&c, &atom("q"), &SurfaceInterpreter, limits(3, 3)).unwrap();
    // Internal case proofs may have temporary dependencies that are discharged
    // above them. Only the root must be independent of every assumption.
    for bit in &query.root_dependencies {
        query.solver.push();
        query.solver.assert(bit);
        assert_eq!(query.solver.check(), SatResult::Unsat);
        query.solver.pop(1);
    }
}

#[test]
fn nested_and_sibling_discharge_labels_follow_the_ancestor_path() {
    let c = context(&[]);
    let goal = implication(atom("p"), implication(atom("q"), atom("p")));
    let (_, d) = bounded(&c, &goal, 2, Some(0)).unwrap();
    let tex = d.proof.to_tex(&goal);
    assert_eq!(tex.matches(r"\Rightarrow I\,[a_{1}]").count(), 1);
    assert!(tex.contains(r"\left[p\right]^{a_{1}}"));
    assert!(tex.contains(r"\Rightarrow I)"));
    let goal = and(vec![
        implication(atom("p"), atom("p")),
        implication(atom("q"), atom("q")),
    ]);
    let (_, d) = bounded(&c, &goal, 3, Some(0)).unwrap();
    let tex = d.proof.to_tex(&goal);
    assert!(tex.contains(r"\left[p\right]^{a_{1}}"));
    assert!(tex.contains(r"\left[q\right]^{a_{2}}"));
    let c = context(&[atom("p"), atom("q")]);
    let body = and(vec![atom("p"), atom("q")]);
    let goal = and(vec![
        implication(atom("p"), body.clone()),
        implication(atom("q"), body),
    ]);
    let (_, d) = bounded(&c, &goal, 4, Some(2)).unwrap();
    let tex = d.proof.to_tex(&goal);
    assert!(tex.contains(r"\left[p\right]^{a_{1}} \qquad q"));
    assert!(tex.contains(r"p \qquad \left[q\right]^{a_{2}}"));
    assert!(!tex.contains(r"\Rightarrow I\,[a_{1},a_{2}]"));
}

#[test]
fn root_bound_applies_before_recording_witness_discharge_alternatives() {
    let mut c = context(&[atom("r"), atom("r")]);
    let original = c.assumptions.keys().copied().collect::<BTreeSet<_>>();
    let parse = |tex| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let source = c
        .check(&parse(r"\exists x \in \mathbb{R}, x=x \land p"))
        .unwrap();
    c.record_external(source, vec![]).unwrap();
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
    let NaturalDeductionResult::Established {
        conclusion,
        mut derivations,
    } = follows_from_natural_deduction(
        &c,
        &parse(r"a=a \land p"),
        &SurfaceInterpreter,
        &mut Checks,
    )
    else {
        panic!()
    };
    c.open_witness(conclusion, vec![], derivations.remove(0))
        .unwrap();
    let witness = c.witnesses[0].assumption;
    let goal = implication(atom("r"), atom("p"));
    // Existing accepted local evidence can have incomparable witness-local and
    // discharged supports. Recording retains both alternatives.
    let checked = c.check(&goal).unwrap();
    let mut local = Derivation::new(NaturalDeductionProof::External);
    local.assumptions.insert(witness);
    c.record(checked, vec![], vec![local]).unwrap();
    let before = c.store_counts();
    let (checked, d) = bounded(&c, &goal, 0, Some(1)).unwrap();
    assert_eq!(d.assumptions, BTreeSet::from([witness]));
    assert!(d.witness_discharges.is_empty());
    assert_eq!(c.store_counts(), before);
    assert!(matches!(
        bounded(&c, &goal, 0, Some(0)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    c.record(checked, vec![], vec![d]).unwrap();
    let fact = c
        .facts()
        .iter()
        .find(|f| f.formula().meaning() == goal)
        .unwrap();
    assert!(
        fact.derivations()
            .any(|d| d.assumptions == original && !d.witness_discharges.is_empty())
    );
}

#[test]
fn implication_query_snapshot_includes_exact_dependencies_and_boolean_bound() {
    let c = context(&[atom("q"), atom("r")]);
    let goal = implication(atom("p"), and(vec![atom("p"), atom("q")]));
    let query = Query::build(
        &c,
        &goal,
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: Some(1),
            ..limits(2, 3)
        },
        "implication_query",
    )
    .unwrap();
    let text = query.solver.to_smt2();
    assert!(!text.contains("(forall"));
    assert!(!text.contains("(exists"));
    assert!(!text.contains("(_ BitVec"));
    assert!(text.contains("dependency_threshold"));
    assert!(text.contains("root_depends"));
    expect_test::expect_file!["../snapshots/implication_query.smt2"].assert_eq(&text);
    let replayed = Solver::new_for_logic("QF_DT").unwrap();
    replayed.from_string(text.as_str());
    assert_eq!(replayed.check(), SatResult::Sat);
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert_eq!(d.assumptions.len(), 1);
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
}

#[test]
fn identical_ambient_formulas_still_have_distinct_dependency_bits() {
    let c = context(&[atom("p"), atom("p")]);
    let goal = and(vec![atom("p"), atom("p")]);
    for (bound, result) in [(1, SatResult::Unsat), (2, SatResult::Sat)] {
        let query = Query::new(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_root_dependencies: Some(bound),
                ..limits(1, 3)
            },
        )
        .unwrap();
        let forced = query
            .proofs
            .inference(
                &query.target,
                ProofRule::AndIntroduction,
                &[query.leaves[0].value.clone(), query.leaves[1].value.clone()],
            )
            .unwrap();
        query.solver.assert(query.root.eq(forced));
        assert_eq!(query.solver.check(), result);
        if result == SatResult::Sat {
            assert_eq!(
                query
                    .decode(&query.solver.get_model().unwrap())
                    .unwrap()
                    .assumptions
                    .len(),
                2
            );
        }
    }
    let c = context(&[]);
    let goal = implication(atom("p"), atom("p"));
    assert!(matches!(
        find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_premises: 0,
                max_root_dependencies: Some(0),
                ..limits(1, 3)
            },
            &Timings::default()
        ),
        Err(SearchError::NoProofWithinBounds(_))
    ));
}

#[test]
fn nary_elimination_uses_one_premise_and_preserves_the_whole_dependency_set() {
    let mut c = context(&[]);
    c.declare_parameter(Variable::new("t"), TypeExpr::Bool);
    let operands = ["p", "q", "r", "s", "t"].map(atom).to_vec();
    let source = and(operands.clone());
    let checked = c.check(&source).unwrap();
    let a = c.assume(checked, vec![]).unwrap();
    for (index, goal) in operands.iter().enumerate() {
        let limits = SearchLimits {
            max_finop_arity: 5,
            ..limits(1, 1)
        };
        let (_, d) =
            find_proof(&c, goal, &SurfaceInterpreter, limits, &Timings::default()).unwrap();
        assert!(
            matches!(&d.proof,NaturalDeductionProof::ConjunctionElimination {operand,..} if *operand==index)
        );
        assert_eq!(d.assumptions, BTreeSet::from([a]));
        assert_eq!(replay(&c, &d.proof, goal), d.assumptions);
    }
    assert!(matches!(
        search(&c, &atom("p"), 1, 1),
        Err(SearchError::Encoding(smt_dt::Error::ArityLimit {
            actual: 5,
            limit: 3
        }))
    ));
    let c = context(&[atom("p"), atom("q")]);
    let query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(2, 2)).unwrap();
    let conclusion = query
        .expressions
        .finite(
            Finop::And,
            &[
                query.proofs.conclusion(&query.leaves[0].value).unwrap(),
                query.proofs.conclusion(&query.leaves[1].value).unwrap(),
            ],
        )
        .unwrap();
    let assembled = query
        .proofs
        .inference(
            &conclusion,
            ProofRule::AndIntroduction,
            &[query.leaves[0].value.clone(), query.leaves[1].value.clone()],
        )
        .unwrap();
    let projected = query
        .proofs
        .inference(&query.target, ProofRule::AndElimination, &[assembled])
        .unwrap();
    query.solver.assert(query.root.eq(projected));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert_eq!(d.assumptions.len(), 2);
}

#[test]
fn elimination_is_immediate_and_requires_a_conjunction() {
    let nested = and(vec![atom("p"), and(vec![atom("q"), atom("r")])]);
    let c = context(&[nested]);
    assert!(matches!(
        search(&c, &atom("r"), 1, 1),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = search(&c, &atom("r"), 2, 1).unwrap();
    assert_eq!(replay(&c, &d.proof, &atom("r")), d.assumptions);
    let c = context(&[Expr::new(RawExpr::Finop(
        Finop::Or,
        vec![atom("p"), atom("q")],
    ))]);
    assert!(matches!(
        search(&c, &atom("p"), 1, 1),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let c = context(&[]);
    let goal = implication(and(vec![atom("p"), atom("q")]), atom("p"));
    assert!(
        bounded(&c, &goal, 2, Some(0))
            .unwrap()
            .1
            .assumptions
            .is_empty()
    );
    let c = context(&[and(vec![atom("p"), atom("p")])]);
    let (_, d) = search(&c, &atom("p"), 1, 1).unwrap();
    assert!(matches!(
        d.proof,
        NaturalDeductionProof::ConjunctionElimination { operand: 0, .. }
    ));
    let c = context(&[]);
    let goal = implication(atom("p"), atom("p"));
    assert!(
        find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_finop_arity: 0,
                ..limits(1, 1)
            },
            &Timings::default()
        )
        .is_ok()
    );
}

#[test]
fn decoded_discarded_intermediates_are_checked_by_the_central_type_checker() {
    let c = context(&[atom("p")]);
    let mut query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(3, 2)).unwrap();
    let p = query.target.clone();
    let one = query
        .expressions
        .encode(&Expr::<()>::new(RawExpr::NatLiteral(1)))
        .unwrap();
    let malformed = query.expressions.implication(&one, &p).unwrap();
    let bad_implication = query
        .proofs
        .inference(
            &malformed,
            ProofRule::ImplicationIntroduction,
            &[query.leaves[0].value.clone()],
        )
        .unwrap();
    let conjunction = query
        .expressions
        .finite(Finop::And, &[p.clone(), malformed])
        .unwrap();
    let assembled = query
        .proofs
        .inference(
            &conjunction,
            ProofRule::AndIntroduction,
            &[query.leaves[0].value.clone(), bad_implication],
        )
        .unwrap();
    let projected = query
        .proofs
        .inference(&p, ProofRule::AndElimination, &[assembled])
        .unwrap();
    query.solver.assert(query.root.eq(projected));
    assert_eq!(query.solver.check(), SatResult::Sat);
    assert!(
        matches!(query.decode(&query.solver.get_model().unwrap()),Err(SearchError::InvalidModel(message)) if message.contains("ill-typed inference conclusion"))
    );
    assert!(search(&c, &atom("p"), 0, 2).is_ok());
}

#[test]
fn generated_predicates_can_use_existing_parameters_absent_from_the_input_facts() {
    let mut c = context(&[atom("p")]);
    c.declare_parameter(Variable::new("x"), TypeExpr::Real);
    let query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(3, 2)).unwrap();
    // Parameters are registered in sorted order: p, q, r, s, x. No contextual fact
    // mentions x, and the predicate x=x is absent from both the goal and facts.
    let variable = query
        .expressions
        .sort()
        .variants
        .iter()
        .find(|v| v.constructor.name().ends_with(".Var"))
        .unwrap();
    let q = variable
        .constructor
        .apply(&[&query.expressions.natural(4)])
        .as_datatype()
        .unwrap();
    assert_eq!(query.expressions.decode(&q).unwrap(), atom("x"));
    let predicate = Expr::new(RawExpr::CmpChain(CmpChain {
        start: atom("x"),
        assertions: vec![(Cmp::Eq, atom("x"))],
    }));
    let mut query = query;
    let eq = query.expressions.encode(&predicate).unwrap();
    let hypothesis = query
        .proofs
        .assumption(&eq, AssumptionRef::Temporary(0), &query.expressions)
        .unwrap();
    let closed = query.expressions.implication(&eq, &eq).unwrap();
    let introduced = query
        .proofs
        .inference(&closed, ProofRule::ImplicationIntroduction, &[hypothesis])
        .unwrap();
    let pair = query
        .expressions
        .finite(Finop::And, &[query.target.clone(), closed])
        .unwrap();
    let assembled = query
        .proofs
        .inference(
            &pair,
            ProofRule::AndIntroduction,
            &[query.leaves[0].value.clone(), introduced],
        )
        .unwrap();
    let projected = query
        .proofs
        .inference(&query.target, ProofRule::AndElimination, &[assembled])
        .unwrap();
    query.solver.assert(query.root.eq(projected));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert_eq!(d.assumptions.len(), 1);
}

#[test]
fn disjunction_introduction_selects_each_nary_operand_without_other_proofs() {
    let values = ["p", "q", "r", "s"].map(atom).to_vec();
    let goal = or(values.clone());
    for (index, premise) in values.iter().enumerate() {
        let c = context(std::slice::from_ref(premise));
        let before = c.store_counts();
        let (checked, d) = find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_finop_arity: 4,
                max_root_dependencies: Some(1),
                ..limits(1, 1)
            },
            &Timings::default(),
        )
        .unwrap();
        assert!(
            matches!(&d.proof,NaturalDeductionProof::DisjunctionIntroduction {operand,..} if *operand==index)
        );
        assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
        assert_eq!(d.assumptions.len(), 1);
        assert_eq!(c.store_counts(), before);
        let mut accepted = c.clone();
        accepted.record(checked, vec![], vec![d]).unwrap();
    }
    let c = context(&[atom("p")]);
    for goal in [or(vec![atom("p")]), or(vec![atom("p"), atom("p")])] {
        let (_, d) = bounded(&c, &goal, 1, Some(1)).unwrap();
        assert!(matches!(
            d.proof,
            NaturalDeductionProof::DisjunctionIntroduction { operand: 0, .. }
        ));
    }
    let repeated = or(vec![atom("p"), atom("p")]);
    let shared = and(vec![repeated.clone(), repeated]);
    assert!(matches!(
        bounded(&c, &shared, 1, Some(1)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = bounded(&c, &shared, 2, Some(1)).unwrap();
    assert_eq!(replay(&c, &d.proof, &shared), d.assumptions);
    assert!(matches!(
        find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            limits(1, 1),
            &Timings::default()
        ),
        Err(SearchError::Encoding(smt_dt::Error::ArityLimit {
            actual: 4,
            limit: 3
        }))
    ));
}

#[test]
fn disjunction_introduction_respects_nesting_and_does_not_eliminate_or_create_assumptions() {
    let c = context(&[atom("q")]);
    let goal = or(vec![atom("p"), or(vec![atom("q"), atom("r")])]);
    assert!(matches!(
        search(&c, &goal, 1, 1),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let (_, d) = search(&c, &goal, 2, 1).unwrap();
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
    let c = context(&[]);
    assert!(matches!(
        search(&c, &or(vec![atom("p"), atom("q")]), 2, 1),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let c = context(&[or(vec![atom("p"), atom("q")])]);
    assert!(matches!(
        search(&c, &atom("p"), 2, 1),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let c = context(&[atom("p")]);
    assert!(matches!(
        bounded(&c, &or(vec![atom("p"), atom("q")]), 1, Some(0)),
        Err(SearchError::NoProofWithinBounds(_))
    ));
    let c = context(&[]);
    for goal in [
        implication(atom("p"), or(vec![atom("p"), atom("q")])),
        or(vec![implication(atom("p"), atom("p")), atom("q")]),
    ] {
        let (checked, d) = bounded(&c, &goal, 2, Some(0)).unwrap();
        assert!(d.assumptions.is_empty());
        assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
        assert!(d.proof.to_tex(&goal).contains(r"\lor I"));
        assert!(d.proof.to_tex(&goal).contains(r"\left[p\right]^{a_{1}}"));
        let mut accepting = c.clone();
        accepting.record(checked, vec![], vec![d]).unwrap();
    }
}

#[test]
fn disjunction_dependencies_are_copied_and_root_bound_selects_an_independent_source() {
    let c = context(&[atom("p"), atom("q")]);
    let goal = or(vec![atom("p"), atom("q")]);
    let query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 1)).unwrap();
    let forced = query
        .proofs
        .inference(
            &query.target,
            ProofRule::OrIntroduction,
            &[query.leaves[0].value.clone()],
        )
        .unwrap();
    query.solver.assert(query.root.eq(forced));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert_eq!(
        d.assumptions,
        query
            .context
            .derivation(query.leaves[0].premise.as_ref().unwrap().derivation)
            .unwrap()
            .assumptions
    );
    query.solver.push();
    query.solver.assert(&query.root_dependencies[1]);
    assert_eq!(query.solver.check(), SatResult::Unsat);
    query.solver.pop(1);
    let mut c = context(&[atom("p")]);
    let checked = c.check(&atom("q")).unwrap();
    c.record(
        checked,
        vec![],
        vec![Derivation::new(NaturalDeductionProof::External)],
    )
    .unwrap();
    let (_, d) = bounded(&c, &goal, 1, Some(0)).unwrap();
    assert!(matches!(
        &d.proof,
        NaturalDeductionProof::DisjunctionIntroduction { operand: 1, .. }
    ));
    assert!(d.assumptions.is_empty());
    assert_eq!(d.proof.supporting_facts(), vec![atom("q")]);
}

#[test]
fn disjunction_model_decoding_rejects_malformed_and_ill_typed_generated_conclusions() {
    let c = context(&[atom("p")]);
    let goal = or(vec![atom("p"), atom("q")]);
    let mut query = Query::new(&c, &goal, &SurfaceInterpreter, limits(3, 2)).unwrap();
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    for (formula, premises) in [
        (query.target.clone(), vec![]),
        (query.target.clone(), vec![query.leaves[0].value.clone(); 2]),
        (
            query.proofs.conclusion(&query.leaves[0].value).unwrap(),
            vec![query.leaves[0].value.clone()],
        ),
    ] {
        let invalid = query
            .proofs
            .inference(&formula, ProofRule::OrIntroduction, &premises)
            .unwrap();
        assert!(matches!(
            Decoder::new(&query, &model)
                .unwrap()
                .decode_value(&invalid, 3),
            Err(SearchError::InvalidModel(_))
        ));
    }
    let one = query
        .expressions
        .encode(&Expr::<()>::new(RawExpr::NatLiteral(1)))
        .unwrap();
    let p = query
        .proofs
        .conclusion(&query.leaves[0].value)
        .unwrap()
        .simplify();
    let bad_or = query
        .expressions
        .finite(Finop::Or, &[p.clone(), one])
        .unwrap();
    let bad = query
        .proofs
        .inference(
            &bad_or,
            ProofRule::OrIntroduction,
            &[query.leaves[0].value.clone()],
        )
        .unwrap();
    assert!(
        matches!(Decoder::new(&query,&model).unwrap().decode_value(&bad,3),Err(SearchError::InvalidModel(message)) if message.contains("ill-typed inference conclusion"))
    );
    let q = query.expressions.encode(&atom("q")).unwrap();
    let wrong_member = query.expressions.finite(Finop::Or, &[q]).unwrap();
    let invalid = query
        .proofs
        .inference(
            &wrong_member,
            ProofRule::OrIntroduction,
            &[query.leaves[0].value.clone()],
        )
        .unwrap();
    assert!(matches!(
        Decoder::new(&query, &model)
            .unwrap()
            .decode_value(&invalid, 3),
        Err(SearchError::InvalidModel(_))
    ));
}

#[test]
fn case_analysis_matches_reference_and_replays_with_capacity_and_dependency_bounds() {
    let p = atom("p");
    let q = atom("q");
    for (facts, goal, slots, capacity, bound, expected) in [
        (
            vec![or(vec![p.clone(), q.clone()])],
            or(vec![q.clone(), p.clone()]),
            3,
            3,
            None,
            true,
        ),
        (
            vec![or(vec![p.clone(), q.clone()])],
            or(vec![q.clone(), p.clone()]),
            3,
            2,
            None,
            false,
        ),
        (
            vec![or(vec![p.clone(), q.clone()])],
            or(vec![q.clone(), p.clone()]),
            2,
            3,
            None,
            false,
        ),
        (vec![or(vec![p.clone()])], p.clone(), 1, 2, None, true),
        (
            vec![or(vec![p.clone(), p.clone()])],
            p.clone(),
            1,
            3,
            Some(1),
            true,
        ),
        (
            vec![or(vec![p.clone(), p.clone()])],
            p.clone(),
            1,
            3,
            Some(0),
            false,
        ),
        (
            vec![or(vec![p.clone(), q.clone()])],
            p.clone(),
            2,
            3,
            None,
            false,
        ),
    ] {
        assert_eq!(
            reference_search(&goal, &facts, slots, capacity, bound),
            expected
        );
        let c = context(&facts);
        let before = c.store_counts();
        match find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_root_dependencies: bound,
                ..limits(slots, capacity)
            },
            &Timings::default(),
        ) {
            Ok((checked, d)) => {
                assert!(expected);
                assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
                assert!(matches!(
                    d.proof,
                    NaturalDeductionProof::DisjunctionElimination { .. }
                ));
                assert_eq!(c.store_counts(), before);
                let mut accepting = c.clone();
                accepting.record(checked, vec![], vec![d]).unwrap();
                assert_eq!(c.facts().len(), facts.len());
            }
            Err(SearchError::NoProofWithinBounds(_)) => assert!(!expected),
            other => panic!("unexpected result: {other:?}"),
        }
        assert_eq!(c.facts().len(), facts.len());
    }
}

#[test]
fn case_analysis_closed_commutativity_and_nested_cases() {
    let p = atom("p");
    let q = atom("q");
    let c = context(&[]);
    let goal = implication(
        or(vec![p.clone(), q.clone()]),
        or(vec![q.clone(), p.clone()]),
    );
    let (_, d) = find_proof(
        &c,
        &goal,
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: Some(0),
            ..limits(4, 3)
        },
        &Timings::default(),
    )
    .unwrap();
    assert!(d.assumptions.is_empty());
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
    let c = context(&[or(vec![p.clone(), or(vec![q.clone(), p.clone()])])]);
    let goal = or(vec![p, q]);
    let (_, d) = search(&c, &goal, 4, 3).unwrap();
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
}

fn temporary_leaf(query: &Query<'_>, index: u64) -> Datatype {
    query.leaves.iter().find(|leaf| matches!(leaf.source, Source::Assumption(AssumptionRef::Temporary(i)) if i == index)).unwrap().value.clone()
}

#[test]
fn case_analysis_discharges_only_the_corresponding_branch_and_keeps_source_support() {
    // The source and both branch conclusions depend on p. Only the first branch
    // discharges p; the second and the source must keep it open.
    let mut c = context(&[atom("p")]);
    let assumption = *c.assumptions.keys().next().unwrap();
    let source = or(vec![atom("p"), atom("q")]);
    let mut evidence = Derivation::new(NaturalDeductionProof::External);
    evidence.assumptions.insert(assumption);
    c.record(c.check(&source).unwrap(), vec![], vec![evidence])
        .unwrap();
    let goal = atom("p");
    let query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 3)).unwrap();
    let forced = query
        .proofs
        .inference(
            &query.target,
            ProofRule::OrElimination,
            &[
                query.leaves[1].value.clone(),
                query.leaves[0].value.clone(),
                query.leaves[0].value.clone(),
            ],
        )
        .unwrap();
    query.solver.assert(query.root.eq(forced));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert_eq!(d.assumptions, BTreeSet::from([assumption]));
    let NaturalDeductionProof::DisjunctionElimination { cases, .. } = &d.proof else {
        panic!()
    };
    assert_eq!(cases[0].discharged, BTreeSet::from([assumption]));
    assert!(cases[1].discharged.is_empty());
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
    let tex = d.proof.to_tex(&goal);
    assert!(tex.contains(r"\left[p\right]^{a_{1}} \qquad p"), "{tex}");
    assert!(d.proof.details(&goal).contains("vacuous discharge"));
    query.solver.assert(query.root_dependencies[0].not());
    assert_eq!(query.solver.check(), SatResult::Unsat);
}

#[test]
fn case_analysis_temporary_dependencies_cannot_escape_other_branches() {
    let source = or(vec![atom("p"), atom("q")]);
    let c = context(std::slice::from_ref(&source));
    let mut query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(1, 3)).unwrap();
    assert_eq!(query.assumption_formulas.len(), query.ambient.len() + 2);
    let p = query.expressions.encode(&atom("p")).unwrap();
    query
        .solver
        .assert(query.assumption_formulas[query.ambient.len()].eq(p));
    let leaf = temporary_leaf(&query, 0);
    let forced = query
        .proofs
        .inference(
            &query.target,
            ProofRule::OrElimination,
            &[query.leaves[0].value.clone(), leaf.clone(), leaf],
        )
        .unwrap();
    query.solver.assert(query.root.eq(forced));
    assert_eq!(query.solver.check(), SatResult::Unsat);
    let invalid = SearchLimits {
        max_rule_slots: usize::MAX,
        max_premises: 3,
        ..limits(0, 0)
    };
    assert!(matches!(
        Query::new(&c, &atom("p"), &SurfaceInterpreter, invalid),
        Err(SearchError::InvalidOptions(_))
    ));
}

#[test]
fn case_analysis_vacuous_discharge_and_malformed_nodes_are_validated() {
    let source = or(vec![atom("p"), atom("q")]);
    let c = context(&[source, atom("r")]);
    let query = Query::new(&c, &atom("r"), &SurfaceInterpreter, limits(1, 3)).unwrap();
    let source = query.leaves[0].value.clone();
    let case = query.leaves[1].value.clone();
    let forced = query
        .proofs
        .inference(
            &query.target,
            ProofRule::OrElimination,
            &[source.clone(), case.clone(), case.clone()],
        )
        .unwrap();
    query.solver.assert(query.root.eq(forced));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    let d = query.decode(&model).unwrap();
    let NaturalDeductionProof::DisjunctionElimination { cases, .. } = &d.proof else {
        panic!()
    };
    assert!(cases.iter().all(|case| case.discharged.is_empty()));
    assert_eq!(replay(&c, &d.proof, &atom("r")), d.assumptions);
    let root = model.eval(&query.root, true).unwrap();
    let tampered = Solver::new_for_logic("QF_DT").unwrap();
    tampered.assert(query.slots[0].eq(&root));
    for (a, bit) in query.dependencies[0].iter().enumerate() {
        // Fabricate omission of the source disjunction dependency.
        tampered.assert(bit.eq(Bool::from_bool(a == 1)));
    }
    assert_eq!(tampered.check(), SatResult::Sat);
    assert!(matches!(
        Decoder::new(&query, &tampered.get_model().unwrap())
            .unwrap()
            .decode_value(&root, 1),
        Err(SearchError::InvalidModel(_))
    ));
    for premises in [
        vec![source.clone()],
        vec![source.clone(), case.clone()],
        vec![case.clone(), case.clone(), case.clone()],
        vec![source.clone(), case.clone(), source.clone()],
        vec![source, case.clone(), case.clone(), case],
    ] {
        let invalid = query
            .proofs
            .inference(&query.target, ProofRule::OrElimination, &premises)
            .unwrap();
        assert!(matches!(
            Decoder::new(&query, &model)
                .unwrap()
                .decode_value(&invalid, 1),
            Err(SearchError::InvalidModel(_))
        ));
    }
    query.solver.assert(query.root_dependencies[0].not());
    assert_eq!(query.solver.check(), SatResult::Unsat);
}

#[test]
fn case_analysis_keeps_cross_branch_and_major_dependencies_independently() {
    for source_depends_on_p in [false, true] {
        let mut c = context(&[atom("p")]);
        let id = *c.assumptions.keys().next().unwrap();
        let source = or(vec![atom("p"), atom("q")]);
        let mut d = Derivation::new(NaturalDeductionProof::External);
        if source_depends_on_p {
            d.assumptions.insert(id);
        }
        c.record(c.check(&source).unwrap(), vec![], vec![d])
            .unwrap();
        c.record(
            c.check(&atom("r")).unwrap(),
            vec![],
            vec![Derivation::new(NaturalDeductionProof::External)],
        )
        .unwrap();
        let goal = if source_depends_on_p {
            atom("r")
        } else {
            atom("p")
        };
        let query = Query::new(&c, &goal, &SurfaceInterpreter, limits(1, 3)).unwrap();
        let branch = query.leaves[if source_depends_on_p { 2 } else { 0 }]
            .value
            .clone();
        let forced = query
            .proofs
            .inference(
                &query.target,
                ProofRule::OrElimination,
                &[query.leaves[1].value.clone(), branch.clone(), branch],
            )
            .unwrap();
        query.solver.assert(query.root.eq(forced));
        assert_eq!(query.solver.check(), SatResult::Sat);
        let model = query.solver.get_model().unwrap();
        let d = query.decode(&model).unwrap();
        assert_eq!(d.assumptions, BTreeSet::from([id]));
        assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
        query.solver.assert(query.root_dependencies[0].not());
        assert_eq!(query.solver.check(), SatResult::Unsat);
    }
}

#[test]
fn case_analysis_renderer_has_branch_local_labels_even_for_shared_assumptions() {
    let c = context(&[or(vec![atom("p"), atom("q")])]);
    let id = AssumptionId(super::super::context::fresh());
    let local_p = ProofInput::local(
        atom("p"),
        NaturalDeductionProof::Assumption { assumption: id },
    );
    // The same assumption can be discharged in one branch and open in another.
    let query = Query::new(&c, &atom("p"), &SurfaceInterpreter, limits(1, 3)).unwrap();
    let source = ProofInput::Context(query.leaves[0].premise.clone().unwrap());
    let proof = NaturalDeductionProof::DisjunctionElimination {
        disjunction: source,
        cases: vec![
            DisjunctionCase {
                premise: local_p.clone(),
                discharged: BTreeSet::from([id]),
                discharged_formulas: BTreeMap::from([(id, atom("p"))]),
            },
            DisjunctionCase {
                premise: local_p,
                discharged: BTreeSet::new(),
                discharged_formulas: BTreeMap::new(),
            },
        ],
    };
    assert_eq!(
        proof.to_tex(&atom("p")),
        r"\dfrac{p \lor q \qquad \left[p\right]^{a_{1}} \qquad p}{p}\;(\lor E\,[a_{1}])"
    );
}

#[test]
fn case_analysis_keeps_identical_ambient_assumption_identities_distinct() {
    let mut c = context(&[atom("p"), atom("p")]);
    let source = or(vec![atom("p"), atom("p")]);
    c.record(
        c.check(&source).unwrap(),
        vec![],
        vec![Derivation::new(NaturalDeductionProof::External)],
    )
    .unwrap();
    let query = Query::new(
        &c,
        &atom("p"),
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: Some(0),
            ..limits(1, 3)
        },
    )
    .unwrap();
    let forced = query
        .proofs
        .inference(
            &query.target,
            ProofRule::OrElimination,
            &[
                query.leaves[2].value.clone(),
                query.leaves[0].value.clone(),
                query.leaves[1].value.clone(),
            ],
        )
        .unwrap();
    query.solver.assert(query.root.eq(forced));
    assert_eq!(query.solver.check(), SatResult::Sat);
    let d = query.decode(&query.solver.get_model().unwrap()).unwrap();
    assert!(d.assumptions.is_empty());
    assert_eq!(replay(&c, &d.proof, &atom("p")), d.assumptions);
    let NaturalDeductionProof::DisjunctionElimination { cases, .. } = &d.proof else {
        panic!()
    };
    assert_eq!(cases[0].discharged.len(), 1);
    assert_eq!(cases[1].discharged.len(), 1);
    assert_ne!(cases[0].discharged, cases[1].discharged);
    assert_eq!(
        cases
            .iter()
            .flat_map(|case| case.discharged.iter().copied())
            .collect::<BTreeSet<_>>(),
        c.assumptions.keys().copied().collect()
    );
}

#[test]
fn modus_ponens_matches_reference_bounds_and_replays_without_changing_context() {
    let p = atom("p");
    let q = atom("q");
    let r = atom("r");
    let pq = implication(p.clone(), q.clone());
    for (facts, goal, slots, capacity, bound, expected) in [
        (vec![pq.clone(), p.clone()], q.clone(), 1, 2, None, true),
        (vec![pq.clone(), p.clone()], q.clone(), 0, 2, None, false),
        (vec![pq.clone(), p.clone()], q.clone(), 1, 1, None, false),
        (vec![pq.clone()], q.clone(), 1, 2, None, false),
        (vec![pq.clone(), r.clone()], q.clone(), 1, 2, None, false),
        (vec![pq.clone(), p.clone()], q.clone(), 1, 2, Some(1), false),
        (vec![pq.clone(), p.clone()], q.clone(), 1, 2, Some(2), true),
        (
            vec![pq.clone(), implication(q.clone(), r.clone()), p.clone()],
            r.clone(),
            1,
            2,
            None,
            false,
        ),
        (
            vec![pq.clone(), implication(q.clone(), r.clone()), p.clone()],
            r.clone(),
            2,
            2,
            None,
            true,
        ),
        (
            vec![
                implication(
                    and(vec![p.clone(), q.clone()]),
                    or(vec![q.clone(), r.clone()]),
                ),
                and(vec![p.clone(), q.clone()]),
            ],
            or(vec![q.clone(), r.clone()]),
            1,
            2,
            None,
            true,
        ),
    ] {
        assert_eq!(
            reference_search(&goal, &facts, slots, capacity, bound),
            expected
        );
        let c = context(&facts);
        let before = c.store_counts();
        let result = find_proof(
            &c,
            &goal,
            &SurfaceInterpreter,
            SearchLimits {
                max_root_dependencies: bound,
                ..limits(slots, capacity)
            },
            &Timings::default(),
        );
        match result {
            Ok((_, d)) => {
                assert!(expected);
                assert!(matches!(
                    d.proof,
                    NaturalDeductionProof::ImplicationElimination { .. }
                ));
                assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
                assert!(bound.is_none_or(|b| d.assumptions.len() <= b));
            }
            Err(SearchError::NoProofWithinBounds(_)) => assert!(!expected),
            other => panic!("unexpected result: {other:?}"),
        }
        assert_eq!(c.store_counts(), before);
    }
}

#[test]
fn modus_ponens_combines_dependencies_and_root_bound_selects_independent_source() {
    let mut c = context(&[atom("p"), atom("r")]);
    let p_id = *c.assumptions.keys().next().unwrap();
    let r_id = *c.assumptions.keys().next_back().unwrap();
    let formula = implication(atom("p"), atom("q"));
    let mut first = Derivation::new(NaturalDeductionProof::External);
    first.assumptions.insert(r_id);
    let mut second = Derivation::new(NaturalDeductionProof::External);
    second.assumptions.insert(p_id);
    c.record(c.check(&formula).unwrap(), vec![], vec![first, second])
        .unwrap();
    let query = Query::new(
        &c,
        &atom("q"),
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: Some(1),
            ..limits(1, 2)
        },
    )
    .unwrap();
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    let d = query.decode(&model).unwrap();
    assert_eq!(d.assumptions, BTreeSet::from([p_id]));
    assert_eq!(replay(&c, &d.proof, &atom("q")), d.assumptions);
    let selected = d
        .proof
        .leaves()
        .into_iter()
        .find(|p| p.expression == formula)
        .unwrap();
    assert_eq!(
        c.derivation(selected.derivation).unwrap().assumptions,
        BTreeSet::from([p_id])
    );
    for bit in [
        query.root_dependencies[0].not(),
        query.root_dependencies[1].clone(),
        query.dependencies[0][0].not(),
    ] {
        query.solver.push();
        query.solver.assert(bit);
        assert_eq!(query.solver.check(), SatResult::Unsat);
        query.solver.pop(1);
    }
    let root = model.eval(&query.root, true).unwrap();
    for extra in [false, true] {
        let tampered = Solver::new_for_logic("QF_DT").unwrap();
        tampered.assert(query.slots[0].eq(&root));
        for (i, bit) in query.dependencies[0].iter().enumerate() {
            tampered.assert(bit.eq(Bool::from_bool(extra && i < 2)));
        }
        assert_eq!(tampered.check(), SatResult::Sat);
        assert!(matches!(
            Decoder::new(&query, &tampered.get_model().unwrap())
                .unwrap()
                .decode_value(&root, 1),
            Err(SearchError::InvalidModel(_))
        ));
    }
}

#[test]
fn modus_ponens_closed_proof_discharges_the_temporary_conjunction_and_can_be_recorded() {
    let mut c = context(&[]);
    let antecedent = and(vec![implication(atom("p"), atom("q")), atom("p")]);
    let goal = implication(antecedent, atom("q"));
    assert!(reference_search(&goal, &[], 4, 2, Some(0)));
    assert!(!reference_search(&goal, &[], 3, 2, Some(0)));
    let before = c.store_counts();
    let (checked, d) = find_proof(
        &c,
        &goal,
        &SurfaceInterpreter,
        SearchLimits {
            max_root_dependencies: Some(0),
            ..limits(4, 2)
        },
        &Timings::default(),
    )
    .unwrap();
    assert_eq!(c.store_counts(), before);
    assert!(d.assumptions.is_empty());
    assert_eq!(replay(&c, &d.proof, &goal), d.assumptions);
    assert!(d.proof.to_tex(&goal).contains(r"\Rightarrow E"));
    assert!(d.proof.to_tex(&goal).contains(r"\left["));
    c.record(checked, vec![], vec![d]).unwrap();
    assert!(search(&c, &goal, 0, 0).unwrap().1.assumptions.is_empty());
}

#[test]
fn modus_ponens_rejects_malformed_models_and_renders_contextual_leaves() {
    let c = context(&[implication(atom("p"), atom("q")), atom("p")]);
    let query = Query::new(&c, &atom("q"), &SurfaceInterpreter, limits(1, 2)).unwrap();
    assert_eq!(query.solver.check(), SatResult::Sat);
    let model = query.solver.get_model().unwrap();
    let d = query.decode(&model).unwrap();
    assert_eq!(
        d.proof.to_tex(&atom("q")),
        r"\dfrac{p \implies q \qquad p}{q}\;(\Rightarrow E)"
    );
    assert!(
        d.proof
            .details(&atom("q"))
            .contains("established antecedent")
    );
    let implication = query.leaves[0].value.clone();
    let p = query.leaves[1].value.clone();
    for premises in [
        vec![],
        vec![implication.clone()],
        vec![implication.clone(), p.clone(), p.clone()],
        vec![p.clone(), implication.clone()],
        vec![p.clone(), p.clone()],
        vec![implication.clone(), implication.clone()],
        vec![implication, query.proofs.unused()],
    ] {
        let invalid = query
            .proofs
            .inference(&query.target, ProofRule::ImplicationElimination, &premises)
            .unwrap();
        assert!(matches!(
            Decoder::new(&query, &model)
                .unwrap()
                .decode_value(&invalid, 1),
            Err(SearchError::InvalidModel(_))
        ));
    }
}
