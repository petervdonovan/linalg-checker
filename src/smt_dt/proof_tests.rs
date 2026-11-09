use super::*;
use crate::Variable;
use z3::{
    SatResult, SortKind,
    ast::{Bool, Dynamic},
};

fn atom(name: &str) -> Expr<()> {
    Expr::new(RawExpr::Variable(Variable::new(name)))
}
fn and(values: Vec<Expr<()>>) -> Expr<()> {
    Expr::new(RawExpr::Finop(Finop::And, values))
}
fn dt(value: &Datatype) -> Dynamic {
    Dynamic::from_ast(value)
}
fn query(
    expressions: &mut ExprDatatype,
    proofs: &ProofDatatype,
    leaves: &[Datatype],
    goal: &Expr<()>,
    n: usize,
    capacity: usize,
) -> (Solver, Datatype, Vec<Datatype>) {
    let root = proofs.constant("root");
    let slots = (0..n)
        .map(|i| proofs.constant(format!("v_{i}")))
        .collect::<Vec<_>>();
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(
        expressions
            .encode(goal)
            .unwrap()
            .eq(proofs.conclusion(&root).unwrap()),
    );
    solver.assert(
        proofs
            .bounded_structure(&root, &slots, leaves, capacity)
            .unwrap(),
    );
    solver.assert(
        proofs
            .rule_constraints(expressions, &slots, capacity)
            .unwrap(),
    );
    (solver, root, slots)
}
fn conjunction(
    proofs: &ProofDatatype,
    expressions: &ExprDatatype,
    children: &[Datatype],
) -> Datatype {
    let conclusions = children
        .iter()
        .map(|p| proofs.conclusion(p).unwrap().simplify())
        .collect::<Vec<_>>();
    let formula = expressions.finite(Finop::And, &conclusions).unwrap();
    proofs
        .inference(&formula, ProofRule::AndIntroduction, children)
        .unwrap()
}

#[test]
fn proof_query_snapshot_is_datatype_only_and_recovers_nested_structure() {
    let mut e = ExprDatatype::with_max_finop_arity("tree_expr", 3);
    let p = ProofDatatype::new("tree", &e);
    let leaves = ["p", "q", "r"].map(|name| {
        p.established(&e.encode(&atom(name)).unwrap(), 0, &e)
            .unwrap()
    });
    let goal = and(vec![atom("p"), and(vec![atom("q"), atom("r")])]);
    let capacity = 3;
    let (solver, root, _) = query(&mut e, &p, &leaves, &goal, 2, capacity);
    let smt = solver.to_smt2();
    expect_test::expect_file!["snapshots/proof_tree.smt2"].assert_eq(&smt);
    assert!(!smt.contains("(forall"));
    assert!(!smt.contains("(exists"));
    assert!(!smt.contains("define-fun-rec"));
    for sort in p.datatypes() {
        for variant in &sort.variants {
            for i in 0..variant.constructor.arity() {
                assert!(matches!(
                    variant.constructor.domain(i),
                    Some(SortKind::Datatype | SortKind::Bool)
                ));
            }
        }
    }
    assert_eq!(solver.check(), SatResult::Sat);
    let value = solver.get_model().unwrap().eval(&root, true).unwrap();
    let ProofNode::Inference {
        conclusion,
        premises,
        rule,
    } = p.inspect(&value, &e).unwrap()
    else {
        panic!()
    };
    assert_eq!(rule, ProofRule::AndIntroduction);
    assert_eq!(e.decode(&conclusion).unwrap(), goal);
    let children = p.read_premises(&premises, capacity).unwrap();
    assert_eq!(children[0], leaves[0]);
    assert!(matches!(
        p.inspect(&children[1], &e),
        Ok(ProofNode::Inference { .. })
    ));
}

#[test]
fn selector_children_are_guarded_immediate_and_sort_aware() {
    let mut e = ExprDatatype::with_max_finop_arity("children_expr", 3);
    let p = ProofDatatype::new("children", &e);
    let formula = e.encode(&atom("p")).unwrap();
    let other = e.encode(&atom("q")).unwrap();
    let leaf = p.established(&formula, 0, &e).unwrap();
    let literal = e
        .encode(&Expr::<()>::new(RawExpr::BoolLiteral(true)))
        .unwrap();
    let mut registry = e.datatypes();
    registry.extend(p.datatypes());
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(selector_child(&registry, &dt(&leaf), &dt(&formula)).unwrap());
    assert_eq!(solver.check(), SatResult::Sat);
    solver.push();
    // The selector of the wrong constructor may equal anything. It must not
    // manufacture a child edge from Context(p) to q.
    let wrong_selector = p.sort().variants[3].accessors[0].apply(&[&leaf]);
    solver.assert(wrong_selector.eq(dt(&other)));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.assert(selector_child(&registry, &dt(&leaf), &dt(&other)).unwrap());
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);
    let node = conjunction(&p, &e, &[leaf.clone(), leaf.clone()]);
    let ProofNode::Inference { premises, .. } = p.inspect(&node, &e).unwrap() else {
        panic!()
    };
    assert_eq!(
        selector_child(&registry, &dt(&node), &dt(&premises))
            .unwrap()
            .simplify()
            .as_bool(),
        Some(true)
    );
    // Proof -> ProofList -> Proof is not an immediate selector edge.
    assert_eq!(
        selector_child(&registry, &dt(&node), &dt(&leaf))
            .unwrap()
            .simplify()
            .as_bool(),
        Some(false)
    );
    assert_eq!(
        selector_child(&registry, &dt(&p.unused()), &dt(&leaf))
            .unwrap()
            .simplify()
            .as_bool(),
        Some(false)
    );
    assert_eq!(
        selector_child(&registry, &dt(&premises), &dt(&leaf))
            .unwrap()
            .simplify()
            .as_bool(),
        Some(true)
    );
    assert_eq!(
        selector_child(
            &registry,
            &dt(&literal),
            &Dynamic::from_ast(&Bool::from_bool(true))
        )
        .unwrap()
        .simplify()
        .as_bool(),
        Some(true)
    );
    let foreign = ExprDatatype::with_max_finop_arity("foreign_children", 3);
    assert!(matches!(
        selector_child(&registry, &dt(&foreign.constant("foreign")), &dt(&leaf)),
        Err(Error::UnregisteredDatatype)
    ));
}

#[test]
fn local_rule_requires_exact_order_arity_and_nonunused_premises() {
    let mut e = ExprDatatype::with_max_finop_arity("local_expr", 3);
    let p = ProofDatatype::new("local", &e);
    let a = p
        .established(&e.encode(&atom("p")).unwrap(), 0, &e)
        .unwrap();
    let b = p
        .established(&e.encode(&atom("q")).unwrap(), 1, &e)
        .unwrap();
    let parent = conjunction(&p, &e, &[a.clone(), b.clone()]);
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(
        p.and_introduction(&e, &[a.clone(), b.clone()], &parent)
            .unwrap(),
    );
    assert_eq!(solver.check(), SatResult::Sat);
    solver.push();
    solver.assert(
        p.and_introduction(&e, &[b.clone(), a.clone()], &parent)
            .unwrap(),
    );
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);
    assert!(matches!(
        p.and_introduction(&e, &[], &parent),
        Err(Error::Malformed(_))
    ));
    solver.push();
    solver.assert(
        p.and_introduction(&e, &[a.clone(), p.unused()], &parent)
            .unwrap(),
    );
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);
    let unary = conjunction(&p, &e, std::slice::from_ref(&a));
    solver.assert(p.and_introduction(&e, &[a], &unary).unwrap());
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(matches!(
        p.established(&parent, 0, &e),
        Err(Error::WrongSort)
    ));
    assert!(matches!(
        p.and_introduction(&e, &[b], &e.constant("not_proof")),
        Err(Error::WrongSort)
    ));
}

#[test]
fn bfs_slot_layout_enforces_sentinels_distinctness_coverage_and_reachability() {
    let mut e = ExprDatatype::with_max_finop_arity("layout_expr", 3);
    let p = ProofDatatype::new("layout", &e);
    let a = p
        .established(&e.encode(&atom("p")).unwrap(), 0, &e)
        .unwrap();
    let b = p
        .established(&e.encode(&atom("q")).unwrap(), 1, &e)
        .unwrap();
    let c = conjunction(&p, &e, &[a.clone(), b.clone()]);
    let d = conjunction(&p, &e, &[c.clone(), a.clone()]);
    let nonadjacent = conjunction(&p, &e, &[a.clone(), c.clone()]);
    let adjacent = conjunction(&p, &e, &[d.clone(), c.clone()]);
    let invalid_child = p
        .inference(
            &e.encode(&and(vec![atom("p"), atom("q")])).unwrap(),
            ProofRule::AndIntroduction,
            &[a.clone(), p.unused()],
        )
        .unwrap();
    let repeated = conjunction(&p, &e, &[c.clone(), c.clone()]);
    let cross_edge = conjunction(&p, &e, &[c.clone(), d.clone()]);
    let cases = [
        (vec![], a.clone(), true),
        (vec![], p.unused(), false),
        (vec![p.unused(), p.unused()], a.clone(), true),
        (vec![p.unused(), c.clone()], c.clone(), false),
        (vec![c.clone(), p.unused()], c.clone(), true),
        // D is unreachable from root C; active slots cannot be padding.
        (vec![c.clone(), d.clone()], c.clone(), false),
        (vec![d.clone(), c.clone()], d.clone(), true),
        (vec![invalid_child.clone()], invalid_child, false),
        (vec![nonadjacent.clone(), c.clone()], nonadjacent, true),
        (
            vec![adjacent.clone(), d.clone(), c.clone()],
            adjacent.clone(),
            true,
        ),
        (
            vec![adjacent.clone(), c.clone(), d.clone()],
            adjacent,
            false,
        ),
        // Equal subproofs share one slot rather than occupying duplicate slots.
        (vec![c.clone(), c.clone()], c.clone(), false),
        (vec![repeated.clone(), c.clone()], repeated, true),
        // A later BFS node may refer back to an earlier slot: D uses C.
        (vec![cross_edge.clone(), c, d], cross_edge, true),
    ];
    for (values, root_value, valid) in cases {
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        let root = p.constant("layout_root");
        let slots = (0..values.len())
            .map(|i| p.constant(format!("layout_{i}")))
            .collect::<Vec<_>>();
        solver.assert(
            p.bounded_structure(&root, &slots, &[a.clone(), b.clone()], 3)
                .unwrap(),
        );
        solver.assert(p.rule_constraints(&e, &slots, 3).unwrap());
        solver.assert(root.eq(&root_value));
        for (slot, value) in slots.iter().zip(&values) {
            solver.assert(slot.eq(value));
        }
        assert_eq!(
            solver.check(),
            if valid {
                SatResult::Sat
            } else {
                SatResult::Unsat
            },
            "{values:?} -> {root_value:?}"
        );
    }
}

#[test]
fn premise_capacity_is_caller_supplied_and_lists_must_terminate() {
    let mut e = ExprDatatype::with_max_finop_arity("capacity_expr", 3);
    let p = ProofDatatype::new("capacity", &e);
    let leaves = [("p", 0), ("q", 1), ("r", 2)].map(|(s, index)| {
        p.established(&e.encode(&atom(s)).unwrap(), index, &e)
            .unwrap()
    });
    let goal = and(vec![atom("p"), atom("q"), atom("r")]);
    for (capacity, expected) in [
        (0, SatResult::Unsat),
        (2, SatResult::Unsat),
        (3, SatResult::Sat),
        (4, SatResult::Sat),
    ] {
        let (solver, _, _) = query(&mut e, &p, &leaves, &goal, 1, capacity);
        assert_eq!(solver.check(), expected);
    }
    let (solver, _, _) = query(&mut e, &p, &leaves, &atom("p"), 4, 0);
    assert_eq!(solver.check(), SatResult::Sat);
    let node = conjunction(&p, &e, &leaves);
    let ProofNode::Inference { premises, .. } = p.inspect(&node, &e).unwrap() else {
        panic!()
    };
    assert!(matches!(
        p.read_premises(&premises, 2),
        Err(Error::Malformed(_))
    ));
    assert_eq!(p.read_premises(&premises, 3).unwrap(), leaves);
    assert!(matches!(
        p.inspect(&p.constant("unevaluated"), &e),
        Err(Error::UnevaluatedTerm)
    ));
    assert!(matches!(
        p.inspect(&e.constant("wrong_sort"), &e),
        Err(Error::WrongSort)
    ));
    assert!(matches!(
        p.read_premises(&p.unused(), 3),
        Err(Error::WrongSort)
    ));
    let empty = p
        .inference(
            &e.encode(&and(vec![])).unwrap(),
            ProofRule::AndIntroduction,
            &[],
        )
        .unwrap();
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(p.rule_constraints(&e, &[empty], 3).unwrap());
    assert_eq!(solver.check(), SatResult::Unsat);
}

/// An independent concrete traversal, with no discovery predicates or SMT indices.
fn reference_bfs(
    proofs: &ProofDatatype,
    e: &ExprDatatype,
    root: &Datatype,
    capacity: usize,
) -> Vec<Datatype> {
    if matches!(
        proofs.inspect(root, e).unwrap(),
        ProofNode::Assumption { .. } | ProofNode::Established { .. }
    ) {
        return vec![];
    }
    let mut queue = vec![root.clone()];
    let mut cursor = 0;
    while cursor < queue.len() {
        let ProofNode::Inference { premises, .. } = proofs.inspect(&queue[cursor], e).unwrap()
        else {
            panic!()
        };
        for child in proofs.read_premises(&premises, capacity).unwrap() {
            match proofs.inspect(&child, e).unwrap() {
                ProofNode::Inference { .. } if !queue.contains(&child) => queue.push(child),
                ProofNode::Unused => panic!("invalid reference graph"),
                _ => (),
            }
        }
        cursor += 1;
    }
    queue
}
fn permutations(values: &[Datatype]) -> Vec<Vec<Datatype>> {
    if values.is_empty() {
        return vec![vec![]];
    }
    let mut result = Vec::new();
    for i in 0..values.len() {
        let mut rest = values.to_vec();
        let first = rest.remove(i);
        for mut tail in permutations(&rest) {
            tail.insert(0, first.clone());
            result.push(tail);
        }
    }
    result
}

#[test]
fn bfs_has_exactly_one_slot_assignment_for_each_fixed_ordered_dag() {
    let mut e = ExprDatatype::with_max_finop_arity("canonical_expr", 3);
    let p = ProofDatatype::new("canonical", &e);
    let a = p
        .established(&e.encode(&atom("p")).unwrap(), 0, &e)
        .unwrap();
    let b = p
        .established(&e.encode(&atom("q")).unwrap(), 1, &e)
        .unwrap();
    let c = conjunction(&p, &e, &[a.clone(), b.clone()]);
    let other = conjunction(&p, &e, &[b.clone(), a.clone()]);
    let l = conjunction(&p, &e, &[c.clone(), a.clone()]);
    let r = conjunction(&p, &e, &[c.clone(), b.clone()]);
    let ordered = conjunction(&p, &e, &[c.clone(), other.clone()]);
    let repeated = conjunction(&p, &e, &[c.clone(), c.clone()]);
    let interspersed = conjunction(&p, &e, &[a.clone(), c.clone(), other]);
    let cross_edge = conjunction(&p, &e, &[c.clone(), l.clone()]);
    let diamond = conjunction(&p, &e, &[l, r]);
    for value in [
        a.clone(),
        c,
        ordered,
        repeated,
        interspersed,
        cross_edge,
        diamond,
    ] {
        let canonical = reference_bfs(&p, &e, &value, 3);
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        let root = p.constant("canonical_root");
        let slots = (0..=canonical.len())
            .map(|i| p.constant(format!("canonical_{i}")))
            .collect::<Vec<_>>();
        solver.assert(
            p.bounded_structure(&root, &slots, &[a.clone(), b.clone()], 3)
                .unwrap(),
        );
        solver.assert(p.rule_constraints(&e, &slots, 3).unwrap());
        solver.assert(root.eq(&value));
        let mut accepted = 0;
        for assignment in permutations(&canonical) {
            solver.push();
            for (slot, value) in slots
                .iter()
                .zip(assignment.iter().chain(std::iter::once(&p.unused())))
            {
                solver.assert(slot.eq(value));
            }
            let expected = assignment == canonical;
            assert_eq!(
                solver.check(),
                if expected {
                    SatResult::Sat
                } else {
                    SatResult::Unsat
                },
                "{value:?}: {assignment:?}"
            );
            accepted += usize::from(expected);
            solver.pop(1);
        }
        assert_eq!(accepted, 1);
    }
}

#[test]
fn bfs_auxiliaries_are_fresh_for_each_fragment_and_absent_positions_are_guarded() {
    let mut e = ExprDatatype::with_max_finop_arity("fragments_expr", 3);
    let p = ProofDatatype::new("fragments", &e);
    let a = p
        .established(&e.encode(&atom("p")).unwrap(), 0, &e)
        .unwrap();
    let b = p
        .established(&e.encode(&atom("q")).unwrap(), 1, &e)
        .unwrap();
    let c = conjunction(&p, &e, &[a.clone(), b.clone()]);
    let d = conjunction(&p, &e, &[c.clone(), a.clone()]);
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    // The first fragment has no non-leaf edges. The second discovers C at its
    // first child, so reusing auxiliary names across fragments would conflict.
    for (name, value, assignment) in [
        ("first", c.clone(), vec![c.clone(), p.unused()]),
        ("second", d.clone(), vec![d, c.clone()]),
    ] {
        let root = p.constant(format!("{name}_root"));
        let slots = (0..2)
            .map(|i| p.constant(format!("{name}_{i}")))
            .collect::<Vec<_>>();
        solver.assert(
            p.bounded_structure(&root, &slots, &[a.clone(), b.clone()], 3)
                .unwrap(),
        );
        solver.assert(p.rule_constraints(&e, &slots, 3).unwrap());
        solver.assert(root.eq(value));
        for (s, v) in slots.iter().zip(assignment) {
            solver.assert(s.eq(v));
        }
    }
    assert_eq!(solver.check(), SatResult::Sat);
    let unused = p.unused();
    let padding = [unused.clone(), unused.clone()];
    solver.assert(
        p.bounded_structure(&a, &padding, &[a.clone(), b], 3)
            .unwrap(),
    );
    let ProofNode::Inference { premises, .. } = p.inspect(&conjunction(&p, &e, &[c]), &e).unwrap()
    else {
        panic!()
    };
    let inapplicable = p.sort().variants[3].accessors[2].apply(&[&unused]);
    solver.assert(inapplicable.eq(Dynamic::from_ast(&premises)));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn boolean_cardinality_matches_exhaustive_small_vectors() {
    for width in 0..=5 {
        let bits = (0..width)
            .map(|_| Bool::fresh_const("cardinality_bit"))
            .collect::<Vec<_>>();
        for bound in 0..=width + 1 {
            let solver = Solver::new_for_logic("QF_DT").unwrap();
            solver.assert(at_most(&bits, bound));
            for mask in 0u32..(1 << width) {
                solver.push();
                for (i, bit) in bits.iter().enumerate() {
                    solver.assert(bit.eq(Bool::from_bool(mask & (1 << i) != 0)));
                }
                assert_eq!(
                    solver.check(),
                    if mask.count_ones() as usize <= bound {
                        SatResult::Sat
                    } else {
                        SatResult::Unsat
                    }
                );
                solver.pop(1);
            }
        }
    }
}

#[test]
fn assumption_sources_and_established_sources_are_distinct_and_inspected() {
    let mut e = ExprDatatype::with_max_finop_arity("identity_expr", 3);
    let p = ProofDatatype::new("identity", &e);
    let formula = e.encode(&atom("p")).unwrap();
    let ambient = p
        .assumption(&formula, AssumptionRef::Ambient(0), &e)
        .unwrap();
    let other = p
        .assumption(&formula, AssumptionRef::Ambient(1), &e)
        .unwrap();
    let temporary = p
        .assumption(&formula, AssumptionRef::Temporary(0), &e)
        .unwrap();
    let established = p.established(&formula, 0, &e).unwrap();
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    for (i, a) in [&ambient, &other, &temporary, &established]
        .iter()
        .enumerate()
    {
        for b in [&ambient, &other, &temporary, &established].iter().take(i) {
            solver.assert((*a).eq(*b).not());
        }
    }
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(matches!(
        p.inspect(&temporary, &e),
        Ok(ProofNode::Assumption {
            source: AssumptionRef::Temporary(0),
            ..
        })
    ));
    assert!(matches!(
        p.inspect(&other, &e),
        Ok(ProofNode::Assumption {
            source: AssumptionRef::Ambient(1),
            ..
        })
    ));
    assert!(matches!(
        p.inspect(&established, &e),
        Ok(ProofNode::Established { source: 0, .. })
    ));
    let parent = p.constant("implication_parent");
    let implication = e.implication(&formula, &formula).unwrap();
    solver.assert(p.implication_introduction(&e, &temporary, &parent).unwrap());
    solver.assert(p.conclusion(&parent).unwrap().eq(implication));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert!(matches!(
        p.inspect(&model.eval(&parent, true).unwrap(), &e),
        Ok(ProofNode::Inference {
            rule: ProofRule::ImplicationIntroduction,
            ..
        })
    ));
}

#[test]
fn single_elimination_rule_selects_any_immediate_conjunct_and_nothing_else() {
    let mut e = ExprDatatype::with_max_finop_arity("eliminate_expr", 5);
    let p = ProofDatatype::new("eliminate", &e);
    let values = ["p", "q", "r", "s", "t"].map(|name| e.encode(&atom(name)).unwrap());
    let formula = e.finite(Finop::And, &values).unwrap();
    let premise = p.established(&formula, 0, &e).unwrap();
    for value in &values {
        let root = p.constant("projection");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(p.and_elimination(&e, &premise, &root).unwrap());
        solver.assert(p.conclusion(&root).unwrap().eq(value));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert!(matches!(
            p.inspect(&model.eval(&root, true).unwrap(), &e),
            Ok(ProofNode::Inference {
                rule: ProofRule::AndElimination,
                ..
            })
        ));
    }
    for formula in [
        e.finite(Finop::Or, &values[..2]).unwrap(),
        e.finite(Finop::And, &[]).unwrap(),
        values[0].clone(),
    ] {
        let premise = p.established(&formula, 1, &e).unwrap();
        let root = p.constant("not_projection");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(p.and_elimination(&e, &premise, &root).unwrap());
        assert_eq!(solver.check(), SatResult::Unsat);
    }
    let nested = e
        .finite(
            Finop::And,
            &[
                values[0].clone(),
                e.finite(Finop::And, &values[1..3]).unwrap(),
            ],
        )
        .unwrap();
    let premise = p.established(&nested, 2, &e).unwrap();
    let root = p.constant("nested_projection");
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(p.and_elimination(&e, &premise, &root).unwrap());
    solver.assert(p.conclusion(&root).unwrap().eq(&values[2]));
    assert_eq!(solver.check(), SatResult::Unsat);
}

#[test]
fn single_disjunction_rule_uses_any_immediate_operand_with_one_proof_premise() {
    let mut e = ExprDatatype::with_max_finop_arity("disjoin_expr", 5);
    let p = ProofDatatype::new("disjoin", &e);
    let values = ["p", "q", "r", "s", "t"].map(|name| e.encode(&atom(name)).unwrap());
    let conclusion = e.finite(Finop::Or, &values).unwrap();
    for (index, value) in values.iter().enumerate() {
        let premise = p.established(value, index as u64, &e).unwrap();
        let root = p.constant("or_parent");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(p.or_introduction(&e, &premise, &root).unwrap());
        solver.assert(p.conclusion(&root).unwrap().eq(&conclusion));
        solver.assert(
            p.bounded_structure(
                &root,
                std::slice::from_ref(&root),
                std::slice::from_ref(&premise),
                1,
            )
            .unwrap(),
        );
        assert_eq!(solver.check(), SatResult::Sat);
        let ProofNode::Inference { rule, premises, .. } = p
            .inspect(&solver.get_model().unwrap().eval(&root, true).unwrap(), &e)
            .unwrap()
        else {
            panic!()
        };
        assert_eq!(rule, ProofRule::OrIntroduction);
        assert_eq!(p.read_premises(&premises, 1).unwrap(), vec![premise]);
    }
    let premise = p.established(&values[0], 0, &e).unwrap();
    for (formula, valid) in [
        (e.finite(Finop::Or, &[]).unwrap(), false),
        (e.finite(Finop::Or, &values[..1]).unwrap(), true),
        (
            e.finite(Finop::Or, &[values[0].clone(), values[0].clone()])
                .unwrap(),
            true,
        ),
        (e.finite(Finop::Or, &values[1..]).unwrap(), false),
        (e.finite(Finop::And, &values).unwrap(), false),
        (e.finite(Finop::Plus, &values).unwrap(), false),
        (values[0].clone(), false),
        (
            e.finite(
                Finop::Or,
                &[
                    e.finite(Finop::Or, &values[..2]).unwrap(),
                    values[2].clone(),
                ],
            )
            .unwrap(),
            false,
        ),
    ] {
        let root = p.constant("or_checked");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(p.or_introduction(&e, &premise, &root).unwrap());
        solver.assert(p.conclusion(&root).unwrap().eq(formula));
        assert_eq!(
            solver.check(),
            if valid {
                SatResult::Sat
            } else {
                SatResult::Unsat
            }
        );
    }
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    let root = p.constant("or_unused");
    solver.assert(p.or_introduction(&e, &p.unused(), &root).unwrap());
    assert_eq!(solver.check(), SatResult::Unsat);
    assert!(matches!(
        p.or_introduction(&e, &premise, &values[0]),
        Err(Error::WrongSort)
    ));
}

#[test]
fn disjunction_elimination_requires_exact_nonempty_cases_and_common_conclusion() {
    let mut e = ExprDatatype::with_max_finop_arity("cases_expr", 3);
    let p = ProofDatatype::new("cases", &e);
    let values = ["p", "q", "r"].map(|name| e.encode(&atom(name)).unwrap());
    let case = p.established(&values[2], 0, &e).unwrap();
    for (operator, count, case_count, valid) in [
        (Finop::Or, 1, 1, true),
        (Finop::Or, 2, 2, true),
        (Finop::Or, 3, 3, true),
        (Finop::Or, 0, 1, false),
        (Finop::Or, 2, 1, false),
        (Finop::Or, 1, 2, false),
        (Finop::And, 2, 2, false),
    ] {
        let formula = e.finite(operator, &values[..count]).unwrap();
        let source = p.established(&formula, 1, &e).unwrap();
        let root = p.constant("case_root");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(
            p.or_elimination(&e, &source, &vec![case.clone(); case_count], &root)
                .unwrap(),
        );
        assert_eq!(
            solver.check(),
            if valid {
                SatResult::Sat
            } else {
                SatResult::Unsat
            }
        );
    }
    let source = p
        .established(&e.finite(Finop::Or, &values[..2]).unwrap(), 1, &e)
        .unwrap();
    let root = p.constant("case_bad");
    assert!(p.or_elimination(&e, &source, &[], &root).is_err());
    for cases in [
        vec![case.clone(), p.unused()],
        vec![case.clone(), p.established(&values[0], 2, &e).unwrap()],
    ] {
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(p.or_elimination(&e, &source, &cases, &root).unwrap());
        assert_eq!(solver.check(), SatResult::Unsat);
    }
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(
        p.or_elimination(&e, &p.unused(), &[case.clone(), case], &root)
            .unwrap(),
    );
    assert_eq!(solver.check(), SatResult::Unsat);
}

#[test]
fn implication_elimination_requires_ordered_matching_premises_and_conclusion() {
    let mut e = ExprDatatype::with_max_finop_arity("apply_expr", 3);
    let proofs = ProofDatatype::new("apply", &e);
    let values = ["p", "q", "r"].map(|name| e.encode(&atom(name)).unwrap());
    let implication = proofs
        .established(&e.implication(&values[0], &values[1]).unwrap(), 0, &e)
        .unwrap();
    let p = proofs.established(&values[0], 1, &e).unwrap();
    let q = proofs.established(&values[1], 2, &e).unwrap();
    for (source, argument, conclusion, valid) in [
        (implication.clone(), p.clone(), values[1].clone(), true),
        (implication.clone(), q.clone(), values[1].clone(), false),
        (p.clone(), implication.clone(), values[1].clone(), false),
        (p.clone(), p.clone(), values[1].clone(), false),
        (implication.clone(), p.clone(), values[2].clone(), false),
        (proofs.unused(), p.clone(), values[1].clone(), false),
        (
            implication.clone(),
            proofs.unused(),
            values[1].clone(),
            false,
        ),
    ] {
        let root = proofs.constant("apply_root");
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(
            proofs
                .implication_elimination(&e, &source, &argument, &root)
                .unwrap(),
        );
        solver.assert(proofs.conclusion(&root).unwrap().eq(conclusion));
        assert_eq!(
            solver.check(),
            if valid {
                SatResult::Sat
            } else {
                SatResult::Unsat
            }
        );
    }
    for children in [
        vec![],
        vec![implication.clone()],
        vec![implication.clone(), p.clone(), q.clone()],
    ] {
        let invalid = proofs
            .inference(&values[1], ProofRule::ImplicationElimination, &children)
            .unwrap();
        let solver = Solver::new_for_logic("QF_DT").unwrap();
        solver.assert(
            proofs
                .implication_elimination(&e, &implication, &p, &invalid)
                .unwrap(),
        );
        assert_eq!(solver.check(), SatResult::Unsat);
    }
}
