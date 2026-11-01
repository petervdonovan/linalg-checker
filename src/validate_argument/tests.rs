use crate::timing::Timings;
use std::collections::{BTreeMap, BTreeSet};

use super::{
    Argument, ArgumentItem, Arguments, StepCheck, Tactic, ToFromMd, free_variables,
    infer_induction_start,
};
use crate::{Environment, RawExpr, TypeExpr, Variable, type_resolver::SymbolicTypeEnvironment};

fn check_deduction(
    context: &crate::natural_deduction::ProofContext,
    conclusion: &crate::Expr<()>,
) -> crate::natural_deduction::NaturalDeductionResult {
    let timings = Timings::default();
    let mut checks = super::quantifier::DimensionChecks {
        evidence: Vec::new(),
        context,
        givens: &[],
        timings: &timings,
    };
    crate::natural_deduction::follows_from_natural_deduction(context, conclusion, &mut checks)
}

const ARGUMENT: &str = r#"# Scalar argument

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $x = x$
2. $x = 0$"#;

fn sentence(argument: &Argument, index: usize) -> &super::ArgumentStep {
    let ArgumentItem::Sentence(step) = &argument.root.steps[index] else {
        panic!("expected a sentence")
    };
    step
}

#[test]
fn pending_argument_round_trips() {
    let argument = Argument::parse_str(ARGUMENT);
    assert_eq!(argument.to_string(), ARGUMENT);
    assert!(argument.root.validation.checks.is_empty());
    assert!(argument.root.steps.iter().all(|item| match item {
        ArgumentItem::Sentence(step) => step.validation.checks.is_empty(),
        ArgumentItem::Goal(goal) => goal.validation.checks.is_empty(),
    }));
}

#[test]
fn proof_sentence_ignores_surrounding_commentary() {
    let commented = r#"# Commented proof

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. **By reflexivity,** $x = x$, *as required.*
2. This step has commentary after the claim: $x = x$ and nothing else."#;
    let uncommented = r#"# Commented proof

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $x = x$
2. $x = x$"#;

    assert_eq!(
        Argument::parse_str(commented),
        Argument::parse_str(uncommented)
    );
}

#[test]
fn nested_proof_sentence_ignores_surrounding_commentary() {
    let argument = Argument::parse_str(
        r#"# Nested commented proof

WTS $x = x$

1. WTS $x = x$

   1. Inside the child goal, $x = x$.
2. Outside the child goal, $x = x$."#,
    );
    let ArgumentItem::Goal(child) = &argument.root.steps[0] else {
        panic!("expected a nested goal")
    };
    assert!(matches!(child.steps[0], ArgumentItem::Sentence(_)));
    assert!(matches!(argument.root.steps[1], ArgumentItem::Sentence(_)));
}

#[test]
#[should_panic(expected = "proof sentence must contain exactly one inline math expression")]
fn proof_sentence_rejects_multiple_math_spans() {
    Argument::parse_str(
        r#"# Ambiguous sentence

WTS $x = x$

1. The two claims $x = x$ and $x = 0$ are ambiguous."#,
    );
}

#[test]
#[should_panic(expected = "proof sentence must contain exactly one inline math expression")]
fn proof_sentence_rejects_commentary_without_math() {
    Argument::parse_str(
        r#"# Missing claim

WTS $x = x$

1. This sentence contains commentary but no mathematical claim."#,
    );
}

#[test]
fn induction_tactic_round_trips_and_establishes_a_goal() {
    let input = r#"# Reflexivity by induction

WTS $n = n$ by induction on $n$

1. WTS $0 = 0$
2. Given:

   - $n = n$

   WTS $n + 1 = n + 1$"#;
    let mut argument = Argument::parse_str(input);
    assert_eq!(argument.to_string(), input);
    assert!(matches!(
        argument.root.tactic,
        Some(Tactic::Induction { ref variable }) if variable.name == "n"
    ));

    argument.validate(2, &Timings::default()).unwrap();
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::TacticEstablished))
    );
    assert!(argument.root.validation.environments_exhaustive);
}

#[test]
fn incomplete_induction_falls_back_to_bounded_validation() {
    let mut argument = Argument::parse_str(
        r#"# Incomplete induction

WTS $n = n$ by induction on $n$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    let StepCheck::IncompleteSubgoals { expected } = argument
        .root
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::IncompleteSubgoals { .. }))
        .expect("missing incomplete-subgoals result")
    else {
        unreachable!()
    };
    assert_eq!(expected[0].as_latex().to_string(), "0 = 0");
    assert!(matches!(
        expected[1].raw,
        RawExpr::Finop(crate::Finop::Forall, _)
    ));
    assert_eq!(
        expected[1].as_latex().to_string(),
        r"\forall n = n, n + 1 = n + 1"
    );
    assert!(argument.root.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
    assert!(
        argument
            .to_string()
            .contains("valid claim, incomplete subgoals")
    );
}

#[test]
fn tactic_bound_natural_appears_in_counterexamples() {
    let mut argument = Argument::parse_str(
        r#"# False induction claim

WTS $n = 0$ by induction on $n$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    let StepCheck::Counterexample { model, .. } = argument
        .root
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Counterexample { .. }))
        .expect("missing counterexample")
    else {
        unreachable!()
    };
    assert!(model.iter().any(|assignment| {
        assignment.as_latex().to_string() == "n = 1" || assignment.as_latex().to_string() == "n = 2"
    }));
}

#[test]
fn induction_binder_is_local_and_may_use_an_arbitrary_name() {
    let mut argument = Argument::parse_str(
        r#"# Local induction binder

WTS $q = q$ by induction on $q$

1. $q = q$
2. WTS $0 = 0$
3. Given:

   - $q = q$

   WTS $q + 1 = q + 1$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Error { .. }
    ));
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::TacticEstablished))
    );
}

#[test]
fn invalid_induction_binders_are_local_goal_errors() {
    let mut collision = Argument::parse_str(
        r#"# Collision

Given:

- $n \in \mathbb{N}$

WTS $n = n$

1. WTS $n = n$ by induction on $n$"#,
    );
    collision.validate(2, &Timings::default()).unwrap();
    let ArgumentItem::Goal(nested) = &collision.root.steps[0] else {
        panic!("expected nested induction goal")
    };
    assert!(matches!(
        nested.validation.checks[0],
        StepCheck::InvalidTactic { .. }
    ));

    let mut absent = Argument::parse_str(
        r#"# Absent binder

WTS $0 = 0$ by induction on $n$"#,
    );
    absent.validate(2, &Timings::default()).unwrap();
    assert!(matches!(
        absent.root.validation.checks[0],
        StepCheck::InvalidTactic { .. }
    ));
}

#[test]
fn induction_start_uses_structural_and_given_constraints_not_truth() {
    fn start(markdown: &str, max_dimension: u64) -> Option<u64> {
        let argument = Argument::parse_str(markdown);
        let Some(Tactic::Induction { variable }) = &argument.root.tactic else {
            panic!("expected induction tactic")
        };
        infer_induction_start(
            &argument.root,
            variable,
            &Environment::default(),
            &SymbolicTypeEnvironment::default(),
            &[],
            max_dimension,
            &Timings::default(),
        )
        .unwrap()
    }

    assert_eq!(
        start("# Zero\n\nWTS $n = n$ by induction on $n$", 3),
        Some(0)
    );
    assert_eq!(
        start(
            "# Vector\n\nGiven:\n\n- $x \\in \\mathbb{R}^{n}$\n\nWTS $0 = 1$ by induction on $n$",
            3,
        ),
        Some(1)
    );
    assert_eq!(
        start(
            "# Later\n\nGiven:\n\n- $n \\ge 2$\n\nWTS $n = n$ by induction on $n$",
            4,
        ),
        Some(2)
    );
}

#[test]
fn forall_binds_first_premise_variables_and_warns_about_irrelevant_premises() {
    let quantified = crate::from_tex::expr(
        &ratex_parser::parse(r"\forall x \in \mathbb{R}^{n}, 0 = 0, x = x").unwrap(),
    )
    .unwrap();
    assert!(free_variables(std::iter::once(&quantified)).is_empty());

    let mut argument = Argument::parse_str(
        r#"# Questionable universal

WTS $0 = 0$

1. Given:

   - $\forall x \in \mathbb{R}, 0 = 0, x = x$

   WTS $0 = 0$"#,
    );
    argument.validate(1, &Timings::default()).unwrap();
    let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(goal.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::QuestionableQuantifier { premises }
            if premises.iter().any(|premise| premise.as_latex().to_string() == "0 = 0")
    )));
}

#[test]
fn universal_claims_share_step_and_goal_validation() {
    let mut argument = Argument::parse_str(
        r#"# Universal claims

WTS $\forall x \in \mathbb{R}, x x \ge 0$

1. $\forall x \in \mathbb{R}, x x \ge 0$"#,
    );
    argument.validate(1, &Timings::default()).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::Reuse { .. },
            ..
        }
    ));

    let mut false_claim = Argument::parse_str(
        r#"# False universal

WTS $\forall x \in \mathbb{R}, x x > 0$"#,
    );
    false_claim.validate(1, &Timings::default()).unwrap();
    let StepCheck::Counterexample { model, .. } = &false_claim.root.validation.checks[0] else {
        panic!("expected a universal counterexample")
    };
    assert!(
        model
            .iter()
            .any(|assignment| assignment.as_latex().to_string() == "x = 0")
    );
}

#[test]
fn universal_naturals_are_bounded_and_empty_domains_are_inconclusive() {
    let mut bounded = Argument::parse_str(
        r#"# Bounded universal

WTS $\forall n \in \mathbb{N}, n = n$"#,
    );
    bounded.validate(2, &Timings::default()).unwrap();
    assert!(bounded.root.validation.checks.iter().all(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
    assert!(!bounded.root.validation.environments_exhaustive);

    let mut vacuous = Argument::parse_str(
        r#"# Vacuous universal

WTS $\forall n > n, n = n$"#,
    );
    vacuous.validate(2, &Timings::default()).unwrap();
    assert!(
        vacuous
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::VacuousQuantifier))
    );
}

#[test]
fn universal_vectors_enumerate_local_dimensions() {
    let mut argument = Argument::parse_str(
        r#"# Universal vectors

WTS $\forall x \in \mathbb{R}^{n}, \left\lVert x \right\rVert_{2}^{2} \ge 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();

    assert!(argument.root.validation.checks.iter().all(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
    assert!(!argument.root.validation.environments_exhaustive);
}

#[test]
fn existential_matching_joins_assignments_across_requirements() {
    let quantified =
        crate::from_tex::expr(&ratex_parser::parse(r"\exists x > 0, x < y").unwrap()).unwrap();
    let mut active = SymbolicTypeEnvironment::default();
    active
        .types
        .insert(crate::Variable::new("y"), crate::TypeExpr::Real);
    let mut context = crate::natural_deduction::ProofContext::default();
    for (v, t) in &active.types {
        context.declare_parameter(v.clone(), t.clone());
    }
    for tex in [r"1 > 0", r"2 > 0", r"1 < y", r"3 < y"] {
        context.assume(
            crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap(),
            Vec::new(),
        );
    }
    assert!(matches!(
        check_deduction(&context, &quantified),
        crate::natural_deduction::NaturalDeductionResult::Established { .. }
    ));
    let mut witness = Argument::parse_str(
        r#"# Existential witness

Given:

- $y \in \mathbb{R}$
- $1 > 0$
- $2 > 0$
- $1 < y$
- $3 < y$

WTS $\exists x > 0, x < y$"#,
    );
    witness.validate(1, &Timings::default()).unwrap();
    let StepCheck::ExistentialWitness { assignments, .. } = witness
        .root
        .validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
        .expect("missing existential witness")
    else {
        unreachable!()
    };
    assert_eq!(assignments.len(), 1);
    assert_eq!(assignments[0].0.name, "x");
    assert_eq!(assignments[0].1.as_latex().to_string(), "1");

    let mut incompatible = Argument::parse_str(
        r#"# Incompatible witnesses

WTS $\exists x > 0, y > 0, x < y, x > y$

1. $1 > 0$
2. $2 > 0$
3. $1 < 2$
4. $3 > 2$"#,
    );
    incompatible.validate(1, &Timings::default()).unwrap();
    assert!(
        incompatible
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
    );
}

#[test]
fn retained_quantifiers_support_exact_reuse_and_nested_bodies() {
    let mut argument = Argument::parse_str(
        r#"# Quantified reuse

Given:

- $a \in \mathbb{R}$
- $a = a$

WTS $\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, y = y\right)$

1. $\exists y \in \mathbb{R}, y = y$
2. $\exists y \in \mathbb{R}, y = y$"#,
    );
    argument.validate(1, &Timings::default()).unwrap();
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::Reuse { .. },
            ..
        }
    ));
    assert!(argument.root.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::Reuse { .. },
            ..
        }
    )));
}

#[test]
fn existential_unification_does_not_leak_inner_binders() {
    let pattern =
        crate::from_tex::expr(&ratex_parser::parse(r"\forall z \in \mathbb{R}, y = z").unwrap())
            .unwrap();
    let candidate =
        crate::from_tex::expr(&ratex_parser::parse(r"\forall z \in \mathbb{R}, z = z").unwrap())
            .unwrap();
    let witness_variable = crate::Variable::new("y");
    let mut unifier = crate::unification::Unifier {
        metavariables: &BTreeSet::from([witness_variable]),
        assignments: BTreeMap::new(),
        pattern_accessible: BTreeSet::new(),
        candidate_accessible: BTreeSet::new(),
        pattern_bound: BTreeSet::new(),
        candidate_bound: BTreeSet::new(),
        bound_forward: BTreeMap::new(),
        bound_reverse: BTreeMap::new(),
        nonce_pairs: BTreeSet::new(),
    };
    assert!(!unifier.expression(&pattern, &candidate));
}

#[test]
fn contextual_existential_elimination_supports_multiple_fresh_binders() {
    use crate::natural_deduction::{NaturalDeductionProof, NaturalDeductionResult, ProofContext};
    let expression = |s: &str| crate::from_tex::expr(&ratex_parser::parse(s).unwrap()).unwrap();
    let mut context = ProofContext::default();
    context.declare_parameter(Variable::new("x"), TypeExpr::Real);
    context.assume(
        expression("P"),
        vec![expression(
            r"\exists u \in \mathbb{R}, v \in \mathbb{R}, x = u + v \land 0 = 0",
        )],
    );
    let NaturalDeductionResult::Established { derivations } =
        check_deduction(&context, &expression("x = a + b"))
    else {
        panic!("missing witness opening")
    };
    assert!(
        matches!(&derivations[0].proof,NaturalDeductionProof::ExistentialElimination{assignments,introduced_types,..} if assignments.len()==2 && introduced_types.keys().cloned().collect::<BTreeSet<_>>()==BTreeSet::from([Variable::new("a"),Variable::new("b")]))
    );
    assert!(matches!(
        check_deduction(&context, &expression("x = a + 1")),
        NaturalDeductionResult::NoMatch
    ));
}

#[test]
fn existential_witness_matching_sees_through_contextual_conjunctions() {
    let expression = |tex: &str| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let active = SymbolicTypeEnvironment {
        types: [
            (Variable::new("x"), TypeExpr::Real),
            (Variable::new("a"), TypeExpr::Real),
        ]
        .into_iter()
        .collect(),
    };
    let quantified = expression(r"\exists w \in \mathbb{R}, x = w");
    let facts = [expression(r"0 = 0 \land x = a")];
    let mut context = crate::natural_deduction::ProofContext::default();
    for (v, t) in &active.types {
        context.declare_parameter(v.clone(), t.clone());
    }
    context.assume(facts[0].clone(), Vec::new());
    let crate::natural_deduction::NaturalDeductionResult::Established { derivations } =
        check_deduction(&context, &quantified)
    else {
        panic!("missing witness")
    };
    assert!(
        matches!(&derivations[0].proof,crate::natural_deduction::NaturalDeductionProof::ExistentialIntroduction{assignments,premises} if assignments[&Variable::new("w")]==expression("a") && premises[0].expression==facts[0])
    );
}

#[test]
fn a_goal_can_be_verified_locally_using_its_witness() {
    let mut argument = Argument::parse_str(
        r#"# Escaping witness

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $x \in \mathbb{R}^{2}$
- $x \in \operatorname{Range}(A)$

WTS $u = u$

1. $x = A u$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks.as_slice(),
        [StepCheck::ExistentialElimination { .. }]
    ));
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Unsat { .. }))
    );
}

#[test]
fn existential_goal_uses_direct_children_and_independent_internal_descendants() {
    let mut direct = Argument::parse_str(
        r#"# Direct child evidence

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. WTS $1 > 0$
2. WTS $1 < y$"#,
    );
    direct.validate(1, &Timings::default()).unwrap();
    assert!(
        direct
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    );

    let mut hidden = Argument::parse_str(
        r#"# Independent internal evidence is exported

WTS $\exists x > 0, x = x$

1. WTS $0 = 0$

   1. $1 > 0$
   2. $1 = 1$"#,
    );
    hidden.validate(1, &Timings::default()).unwrap();
    assert!(
        hidden
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    );
}

#[test]
fn quantified_binders_must_be_fresh_and_introduced_in_premises() {
    let mut shadowed = Argument::parse_str(
        r#"# Shadowed binder

Given:

- $x \in \mathbb{R}$

WTS $\forall x \in \mathbb{R}, x = x$"#,
    );
    shadowed.validate(1, &Timings::default()).unwrap();
    assert!(
        shadowed
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
    );

    let mut body_only = Argument::parse_str(
        r#"# Body-only variable

WTS $\exists 0 = 0, x = x$"#,
    );
    body_only.validate(1, &Timings::default()).unwrap();
    assert!(
        body_only
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
    );
}

#[test]
fn failed_children_do_not_invalidate_the_goal() {
    let mut argument = Argument::parse_str(ARGUMENT);
    argument.validate(0, &Timings::default()).unwrap();

    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::Counterexample { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
}

#[test]
fn nested_goals_round_trip_and_validate_locally() {
    let input = r#"# Nested

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. WTS $x = x$

   1. $x = 0$
   2. $x = x$
2. Given:

   - $y \in \mathbb{R}$

   WTS $y = y$"#;
    let mut argument = Argument::parse_str(input);
    assert_eq!(argument.to_string(), input);
    argument.validate(0, &Timings::default()).unwrap();

    let ArgumentItem::Goal(first) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(matches!(
        first.validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
    assert!(matches!(
        &first.steps[0],
        ArgumentItem::Sentence(step)
            if matches!(step.validation.checks[0], StepCheck::Counterexample { .. })
    ));

    let ArgumentItem::Goal(second) = &argument.root.steps[1] else {
        panic!("expected scoped goal")
    };
    assert!(matches!(
        second.validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
}

#[test]
fn inconsistent_givens_are_reported_on_the_goal_only() {
    let mut argument = Argument::parse_str(
        r#"# Inconsistent

Given:

- $n < 0$

WTS $n = n$

1. $n = 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::InconsistentGivens {
            max_dimension: None
        }
    ));
    assert!(sentence(&argument, 0).validation.checks.is_empty());
}

#[test]
fn unbound_child_errors_are_localized() {
    let mut argument = Argument::parse_str(
        r#"# Unbound child

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $y = y$
2. $x = x$"#,
    );
    argument.validate(0, &Timings::default()).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Error { .. }
    ));
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
}

#[test]
fn local_givens_do_not_escape_their_goal() {
    let mut argument = Argument::parse_str(
        r#"# Scoped givens

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. Given:

   - $x = 0$

   WTS $x \le 0$
2. $x = 0$"#,
    );
    argument.validate(0, &Timings::default()).unwrap();
    let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(matches!(
        goal.validation.checks[0],
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    ));
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::Counterexample { .. }
    ));
}

#[test]
fn partially_feasible_givens_are_not_reported_as_vacuous() {
    let mut argument = Argument::parse_str(
        r#"# Partial givens

Given:

- $A = A$

WTS $A = A$

1. Given:

   - $A \in \mathbb{R}^{2 \times 2}$

   WTS $A = A$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(goal.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
    assert!(
        !goal
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::InconsistentGivens { .. }))
    );
}

#[test]
#[should_panic(expected = "goal body must be an ordered list")]
fn annotated_output_is_not_parseable_as_input() {
    let mut argument = Argument::parse_str(ARGUMENT);
    argument.validate(0, &Timings::default()).unwrap();
    Argument::parse_str(&argument.to_string());
}

#[test]
fn collection_records_argument_errors_and_continues() {
    let invalid = Argument::parse_str(
        r#"# Invalid

Given:

- $A \in \mathbb{R}^{n p}$

WTS $A = A$"#,
    );
    let valid = Argument::parse_str(ARGUMENT);
    let mut arguments = Arguments(vec![invalid, valid]);
    arguments.validate(0, &Timings::default());
    assert!(arguments.0[0].error.is_some());
    assert!(arguments.0[1].error.is_none());
    assert!(!arguments.0[1].root.validation.checks.is_empty());
}

#[test]
fn ellipsis_local_givens_do_not_escape_to_siblings() {
    let mut argument = Argument::parse_str(
        r"# Local interpretation

Given:

- $n = 2$
- $c \in \operatorname{Seq}_{n}(\mathbb{R})$
- $d \in \operatorname{Seq}_{n}(\mathbb{R})$

WTS $0 = 0$

1. Given:

   - $\operatorname{diag}(c) = \operatorname{diag}(d)$

   WTS $\operatorname{diag}(c_{1}, \ldots, d_{n}) = \operatorname{diag}(c)$
2. $\operatorname{diag}(c_{1}, \ldots, d_{n}) = \operatorname{diag}(c)$",
    );
    argument.validate(2, &Timings::default()).unwrap();
    let ArgumentItem::Goal(child) = &argument.root.steps[0] else {
        panic!("expected goal")
    };
    assert!(child.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
    assert!(
        sentence(&argument, 1)
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Error { .. }))
    );
    assert!(argument.root.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
}

#[test]
fn synthesis_minimum_endpoint_does_not_filter_validation_environments() {
    let mut argument = Argument::parse_str(
        r"# Private candidate bound

Given:

- $n \in \mathbb{N}$
- $c \in \operatorname{Seq}_{n}(\mathbb{R})$

WTS $\operatorname{diag}(c_{1}, \ldots, c_{n}) = \operatorname{diag}(c)$",
    );
    argument.validate(2, &Timings::default()).unwrap();
    // Synthesis needs two anchor positions, but the interpreted map also has a
    // perfectly meaningful one-element instance in the main validation loop.
    assert_eq!(
        argument
            .root
            .validation
            .checks
            .iter()
            .filter(|check| matches!(
                check,
                StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
            ))
            .count(),
        2
    );
}

#[test]
fn natural_deduction_instantiates_explicit_and_exported_universals() {
    for source in [
        r#"# Explicit universal

Given:

- $y \in \mathbb{R}$

- $\forall x > 0, x < y$

- $1 > 0$

WTS $1 < y$"#,
        r#"# Exported universal

Given:

- $y \in \mathbb{R}$

WTS $y = y$

1. Given:

   - $a \in \mathbb{R}$

   WTS $a = a$"#,
    ] {
        let mut argument = Argument::parse_str(source);
        argument.validate(2, &Timings::default()).unwrap();
        assert!(argument.root.validation.checks.iter().any(|c| matches!(c, StepCheck::NaturalDeduction { proof: crate::natural_deduction::NaturalDeductionProof::UniversalElimination { .. }, .. })), "{:?}", argument.root.validation);
        assert!(argument.to_string().contains("universal elimination"));
    }
}

#[test]
fn natural_deduction_generalizes_an_established_instance() {
    let mut argument = Argument::parse_str(
        r#"# Generalization

Given:

- $a \in \mathbb{R}$

WTS $\forall x \in \mathbb{R}, x = x$

1. $a = a$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(argument.root.validation.checks.iter().any(|c| matches!(c, StepCheck::NaturalDeduction { proof: crate::natural_deduction::NaturalDeductionProof::UniversalIntroduction { .. }, .. })), "{:?}", argument.root.validation);
}

#[test]
fn natural_deduction_implication_introduction_is_explicit_and_exportable() {
    let mut argument = Argument::parse_str(
        r#"# Discharged implication

Given:

- $x \in \mathbb{R}$

WTS $\exists t \in \mathbb{R}, t = t, x > 0 \implies x > 0$

1. $1 = 1$

2. Given:

   - $x > 0$

   WTS $x = 0$

   1. $x > 0 \implies x > 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    let ArgumentItem::Goal(child) = &argument.root.steps[1] else {
        panic!()
    };
    assert!(matches!(
        &sentence_child(child, 0).validation.checks[0],
        StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::ImplicationIntroduction { .. },
            ..
        }
    ));
    assert!(
        child
            .validation
            .checks
            .iter()
            .any(|c| matches!(c, StepCheck::Counterexample { .. }))
    );
    assert!(argument.root.validation.checks.iter().any(|c| matches!(c,StepCheck::ExistentialWitness { supporting_facts, .. } if supporting_facts.contains(&sentence_child(child,0).sentence))));
}

fn sentence_child(goal: &super::Goal, index: usize) -> &super::ArgumentStep {
    let ArgumentItem::Sentence(step) = &goal.steps[index] else {
        panic!("expected sentence")
    };
    step
}

#[test]
fn a_failed_child_still_exports_independent_validated_facts() {
    let mut argument = Argument::parse_str(
        r#"# Independent fact from failed block

WTS $\exists x > 0, x = x$

1. WTS $0 = 1$

   1. $1 > 0$

   2. $1 = 1$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|c| matches!(c, StepCheck::ExistentialWitness { .. }))
    );
}

#[test]
fn natural_deduction_does_not_instantiate_incompatible_vector_dimensions() {
    let mut argument = Argument::parse_str(
        r#"# Incompatible witness dimensions

Given:

- $y \in \mathbb{R}^{3}$

WTS $\exists x \in \mathbb{R}^{2}, x = y$

1. $y = y$"#,
    );
    argument.validate(3, &Timings::default()).unwrap();
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .all(|c| !matches!(c, StepCheck::ExistentialWitness { .. }))
    );
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|c| matches!(c, StepCheck::QuantifierInconclusive { .. }))
    );
}

#[test]
fn independent_export_does_not_downgrade_local_deduction() {
    let mut argument = Argument::parse_str(
        r#"# Bounded exported statement

Given:

- $x \in \mathbb{R}$

WTS $x > 0 \implies x > 0$

1. Given:

   - $n \in \mathbb{N}$
   - $x > 0$

   WTS $n = n$

   1. $x > 0 \implies x > 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(argument.root.validation.environments_exhaustive);
    assert!(argument.root.validation.checks.iter().all(|c| matches!(
        c,
        StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
    )));
}

#[test]
fn natural_deduction_type_errors_are_local_and_goals_can_open_witnesses() {
    let mut argument = Argument::parse_str(
        r#"# Ill typed implication

WTS $1 \implies 0 = 0$

1. $0 = 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(argument.root.validation.checks.iter().any(|c| matches!(
        c,
        StepCheck::Error { .. } | StepCheck::DimensionallyInvalid { .. }
    )));

    let mut argument = Argument::parse_str(
        r#"# Opening a witness in the conclusion

Given:

- $\exists x \in \mathbb{R}, x > 0$

WTS $a > 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|c| matches!(c, StepCheck::ExistentialElimination { .. }))
    );
}

#[test]
fn likely_premises_support_verified_reuse_without_rechecking_their_truth() {
    let mut argument = Argument::parse_str(
        r#"# Local inference status

Given:

- $A \in \mathbb{R}^{n \times n}$

WTS $A = A$

1. $A = A$
2. $A = A$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(!sentence(&argument, 0).validation.environments_exhaustive);
    assert!(sentence(&argument, 1).validation.environments_exhaustive);
    assert!(matches!(
        sentence(&argument, 1).validation.checks.as_slice(),
        [StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::Reuse { .. },
            ..
        }]
    ));
    assert!(argument.root.validation.environments_exhaustive);
}

#[test]
fn fallback_results_are_aggregated_before_a_fact_enters_the_context() {
    let mut argument = Argument::parse_str(
        r#"# Reject before admission

Given:

- $n \in \mathbb{N}$

WTS $0 = 1$

1. $n = 0$
2. $n = 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    for i in 0..2 {
        assert!(
            sentence(&argument, i)
                .validation
                .checks
                .iter()
                .any(|c| matches!(c, StepCheck::Counterexample { .. }))
        );
        assert!(
            !sentence(&argument, i)
                .validation
                .checks
                .iter()
                .any(|c| matches!(
                    c,
                    StepCheck::NaturalDeduction {
                        proof: crate::natural_deduction::NaturalDeductionProof::Reuse { .. },
                        ..
                    }
                ))
        );
    }
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|c| matches!(c, StepCheck::Counterexample { .. }))
    );
}

#[test]
fn a_goal_witness_opening_is_valid_locally_but_is_not_exported() {
    let mut argument = Argument::parse_str(
        r#"# Local witness

Given:

- $\exists x \in \mathbb{R}, x > 0$

WTS $a > 0$"#,
    );
    let mut context = crate::natural_deduction::ProofContext::default();
    let mut run = super::ValidationRun {
        timings: Timings::default(),
        max_dimension: 2,
        next_tracker: 0,
        givens: Vec::new(),
        lexical_expressions: Vec::new(),
        interpretations: BTreeMap::new(),
    };
    let outcome =
        super::natural_deduction::validate_goal(&mut argument.root, &mut context, &mut run, None)
            .unwrap();
    assert!(outcome.validated);
    assert!(!outcome.exported);
    assert!(!context.types.types.contains_key(&Variable::new("a")));
    assert!(context.facts().is_empty());
}

#[test]
fn instantiation_requires_symbolic_dimension_compatibility() {
    use crate::natural_deduction::{NaturalDeductionProof, NaturalDeductionResult, ProofContext};
    let expression = |tex: &str| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let mut context = ProofContext::default();
    for name in ["n", "m"] {
        context.declare_parameter(Variable::new(name), TypeExpr::Nat);
    }
    context.declare_parameter(
        Variable::new("y"),
        TypeExpr::Matrix(expression("m"), expression("1")),
    );
    context.assume(
        expression(r"\forall x \in \mathbb{R}^{n}, x = x"),
        Vec::new(),
    );
    let target = expression("y = y");
    let timings = Timings::default();
    let mut checks = super::quantifier::DimensionChecks {
        evidence: Vec::new(),
        context: &context,
        givens: &[],
        timings: &timings,
    };
    assert!(!matches!(
        crate::natural_deduction::follows_from_natural_deduction(&context, &target, &mut checks),
        NaturalDeductionResult::Established { .. }
    ));
    let equality = crate::preprocessing::prepare_expression(
        &context.types,
        &expression("n = m"),
        super::POSITIVE,
    )
    .unwrap();
    let mut checks = super::quantifier::DimensionChecks {
        evidence: Vec::new(),
        context: &context,
        givens: std::slice::from_ref(&equality),
        timings: &timings,
    };
    let NaturalDeductionResult::Established { derivations } =
        crate::natural_deduction::follows_from_natural_deduction(&context, &target, &mut checks)
    else {
        panic!("symbolic equality should establish compatible dimensions")
    };
    assert!(matches!(
        derivations[0].proof,
        NaturalDeductionProof::UniversalElimination { .. }
    ));
}

#[test]
fn likely_instance_supports_verified_universal_introduction() {
    let mut argument = Argument::parse_str(
        r#"# Generalize an accepted instance

Given:

- $n \in \mathbb{N}$

WTS $\forall k \in \mathbb{N}, k = k$

1. $n = n$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(!sentence(&argument, 0).validation.environments_exhaustive);
    assert!(argument.root.validation.environments_exhaustive);
    assert!(matches!(
        argument.root.validation.checks.as_slice(),
        [StepCheck::NaturalDeduction {
            proof: crate::natural_deduction::NaturalDeductionProof::UniversalIntroduction { .. },
            ..
        }]
    ));
}

#[test]
fn witness_acceptance_selects_the_first_suitable_source() {
    let mut argument = Argument::parse_str(
        r#"# Select a witness source

Given:

- $\exists x \in \mathbb{R}, x > 0$
- $\exists y \in \mathbb{R}, y > 0 \land y < 1$

WTS $a > 0$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(
        matches!(argument.root.validation.checks.as_slice(),[StepCheck::ExistentialElimination{fact,..}] if fact==&argument.root.givens[0])
    );
}

#[test]
fn undefined_instantiation_is_not_mislabeled_as_verified_or_likely() {
    let mut argument = Argument::parse_str(
        r#"# Undefined instantiation

Given:

- $\forall x \in \mathbb{R}, x = x$

WTS $\left(-1\right)^{\frac{1}{2}} = \left(-1\right)^{\frac{1}{2}}$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    assert!(argument.root.validation.checks.iter().any(|c| matches!(
        c,
        StepCheck::MayBeUndefined { .. } | StepCheck::Error { .. }
    )));
    assert!(!argument.root.validation.checks.iter().any(|c| matches!(
        c,
        StepCheck::NaturalDeduction { .. } | StepCheck::Unsat { .. }
    )));
}

#[test]
fn accepted_dimension_facts_are_usable_and_their_scope_dependencies_are_retained() {
    use crate::natural_deduction::{NaturalDeductionResult, ProofContext};
    let expression = |tex: &str| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let mut context = ProofContext::default();
    for name in ["n", "m"] {
        context.declare_parameter(Variable::new(name), TypeExpr::Nat);
    }
    context.declare_parameter(
        Variable::new("y"),
        TypeExpr::Matrix(expression("m"), expression("1")),
    );
    context.assume(
        expression(r"\forall x \in \mathbb{R}^{n}, x = x"),
        Vec::new(),
    );
    let parent = context.clone();
    context.enter_scope();
    let local = context.assume(expression("1 > 0"), Vec::new());
    // Simulate a fact already accepted by fallback. It is available to subsequent
    // dimension checks even though it is not one of their lexical givens.
    context.record_external(expression("n = m"), Vec::new());
    let equality = context
        .facts()
        .iter()
        .find(|f| f.expression == expression("n = m"))
        .unwrap()
        .derivations[0]
        .id;
    let target = expression("y = y");
    let timings = Timings::default();
    let mut checks = super::quantifier::DimensionChecks {
        context: &context,
        givens: &[],
        timings: &timings,
        evidence: Vec::new(),
    };
    let NaturalDeductionResult::Established { derivations } =
        crate::natural_deduction::follows_from_natural_deduction(&context, &target, &mut checks)
    else {
        panic!("accepted dimension equality should be usable");
    };
    assert!(
        derivations.iter().all(
            |d| d.assumptions.contains(&local) && d.side_condition_premises.contains(&equality)
        )
    );
    context.record(target.clone(), Vec::new(), derivations);
    assert!(
        !context
            .exportable_to(&parent)
            .iter()
            .any(|f| f.expression == target)
    );
}

#[test]
fn undefined_references_are_reported_without_guessing_a_new_variable() {
    use crate::type_resolver::{TypeError, analyze_formula};
    let expression = |tex: &str| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    for tex in ["x = x", r"\forall y \in \mathbb{R}, x = y"] {
        let error =
            analyze_formula(&SymbolicTypeEnvironment::default(), &expression(tex)).unwrap_err();
        assert!(matches!(&error, TypeError::UndefinedVariable(v) if v.name == "x"));
        assert_eq!(error.to_string(), "reference to undefined variable $x$");
    }
    let mut argument = Argument::parse_str("# Undefined reference\n\nWTS $x = x$");
    argument.validate(2, &Timings::default()).unwrap();
    assert!(
        argument
            .to_string()
            .contains("reference to undefined variable $x$")
    );
    assert!(!argument.to_string().contains("missing type"));

    // Name-based inference remains available when a variable is introduced.
    let mut declared =
        Argument::parse_str("# Introduced variable\n\nGiven:\n\n- $x = x$\n\nWTS $x = x$");
    declared.validate(2, &Timings::default()).unwrap();
    assert!(declared.to_string().contains("✅ repeats established fact"));
}

#[test]
fn quantifier_failure_uses_user_facing_language() {
    let mut argument = Argument::parse_str(
        r#"# Quantifier limitation

WTS $\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right) \land x = x$"#,
    );
    argument.validate(2, &Timings::default()).unwrap();
    let rendered = argument.to_string();
    assert!(rendered.contains("verification failed to handle the quantifiers in this formula"));
    assert!(!rendered.contains("SMT"));
    assert!(!rendered.contains("backend"));
}

#[test]
fn reuse_rendering_distinguishes_repetition_from_contextual_views() {
    use crate::natural_deduction::NaturalDeductionProof;
    for (source, conclusion, exact) in [
        ("x > 0", "x > 0", true),
        (r"x > 0 \land x < 2", "x > 0", false),
    ] {
        let input = format!(
            "# Contextual reuse\n\nGiven:\n\n- $x \\in \\mathbb{{R}}$\n- ${source}$\n\nWTS ${conclusion}$"
        );
        let mut argument = Argument::parse_str(&input);
        argument.validate(2, &Timings::default()).unwrap();
        let StepCheck::NaturalDeduction {
            proof: NaturalDeductionProof::Reuse { premise },
            supporting_facts,
        } = &argument.root.validation.checks[0]
        else {
            panic!("expected structured reuse: {:?}", argument.root.validation);
        };
        assert_eq!(premise.expression, argument.root.givens[1]);
        assert_eq!(supporting_facts, &[argument.root.givens[1].clone()]);
        let rendered = argument.to_string();
        if exact {
            assert!(rendered.contains("✅ repeats established fact"));
            assert!(!rendered.contains("This follows from the following facts"));
        } else {
            assert!(rendered.contains("✅ follows from established fact"));
            assert!(!rendered.contains("✅ repeats established fact"));
        }
    }
}

#[test]
fn an_elaborated_context_view_retains_its_source_in_the_explanation() {
    use crate::natural_deduction::{NaturalDeductionProof, NaturalDeductionResult, ProofContext};
    let expression = |tex: &str| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap();
    let mut context = ProofContext::default();
    context.declare_parameter(Variable::new("x"), TypeExpr::Real);
    let source = expression("0 < x");
    let alternative = expression("x > 0");
    context.assume(source.clone(), vec![alternative.clone()]);
    let NaturalDeductionResult::Established { derivations } =
        check_deduction(&context, &alternative)
    else {
        panic!("expected reuse of the context view");
    };
    assert!(
        matches!(&derivations[0].proof, NaturalDeductionProof::Reuse { premise } if premise.alternative == Some(0) && premise.expression == source)
    );
    let mut argument = Argument::parse_str("# Context view\n\nWTS $x > 0$");
    argument
        .root
        .validation
        .checks
        .push(StepCheck::NaturalDeduction {
            proof: derivations[0].proof.clone(),
            supporting_facts: vec![source.clone()],
        });
    let rendered = argument.to_string();
    assert!(rendered.contains("✅ follows from established fact"));
    assert!(rendered.contains(&format!("- ${}$", source.as_latex())));
    assert!(!rendered.contains("✅ repeats established fact"));
}
