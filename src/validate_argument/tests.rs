use std::collections::{BTreeMap, BTreeSet};

use super::{
    Argument, ArgumentItem, Arguments, StepCheck, Tactic, ToFromMd, free_variables,
    infer_induction_start,
};
use crate::{Environment, RawExpr, type_resolver::SymbolicTypeEnvironment};

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

    argument.validate(2).unwrap();
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::TacticEstablished))
    );
    assert!(!argument.root.validation.environments_exhaustive);
}

#[test]
fn incomplete_induction_falls_back_to_bounded_validation() {
    let mut argument = Argument::parse_str(
        r#"# Incomplete induction

WTS $n = n$ by induction on $n$"#,
    );
    argument.validate(2).unwrap();
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
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Unsat { .. }))
    );
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
    argument.validate(2).unwrap();
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
    argument.validate(2).unwrap();
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
    collision.validate(2).unwrap();
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
    absent.validate(2).unwrap();
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
            max_dimension,
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
    argument.validate(1).unwrap();
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
    argument.validate(1).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Unsat { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::EstablishedByFact { .. }
    ));

    let mut false_claim = Argument::parse_str(
        r#"# False universal

WTS $\forall x \in \mathbb{R}, x x > 0$"#,
    );
    false_claim.validate(1).unwrap();
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
    bounded.validate(2).unwrap();
    assert!(
        bounded
            .root
            .validation
            .checks
            .iter()
            .all(|check| matches!(check, StepCheck::Unsat { .. }))
    );
    assert!(!bounded.root.validation.environments_exhaustive);

    let mut vacuous = Argument::parse_str(
        r#"# Vacuous universal

WTS $\forall n > n, n = n$"#,
    );
    vacuous.validate(2).unwrap();
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
    argument.validate(2).unwrap();

    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .all(|check| matches!(check, StepCheck::Unsat { .. }))
    );
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
    let spec = super::analyze_quantifier(&quantified, &active).unwrap();
    let facts = [r"1 > 0", r"2 > 0", r"1 < y", r"3 < y"]
        .map(|tex| crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap());
    assert!(
        super::quantifier::find_existential_witness(
            &spec,
            &active,
            &Environment::default(),
            &facts,
        )
        .is_some(),
        "direct matching failed for spec {:?} and facts {:?}",
        spec.introduced,
        facts
    );
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
    witness.validate(1).unwrap();
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
    incompatible.validate(1).unwrap();
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
    argument.validate(1).unwrap();
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::EstablishedByFact { .. }
    ));
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::EstablishedByFact { .. }))
    );
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
    let mut unifier = super::Unifier {
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
fn existential_goal_uses_direct_children_but_not_internal_descendants() {
    let mut direct = Argument::parse_str(
        r#"# Direct child evidence

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. WTS $1 > 0$
2. WTS $1 < y$"#,
    );
    direct.validate(1).unwrap();
    assert!(
        direct
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    );

    let mut hidden = Argument::parse_str(
        r#"# Internal evidence stays local

WTS $\exists x > 0, x = x$

1. WTS $0 = 0$

   1. $1 > 0$
   2. $1 = 1$"#,
    );
    hidden.validate(1).unwrap();
    assert!(
        hidden
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
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
    shadowed.validate(1).unwrap();
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
    body_only.validate(1).unwrap();
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
    argument.validate(0).unwrap();

    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Unsat { .. }
    ));
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::Counterexample { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::Unsat { .. }
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
    argument.validate(0).unwrap();

    let ArgumentItem::Goal(first) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(matches!(
        first.validation.checks[0],
        StepCheck::Unsat { .. }
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
        StepCheck::Unsat { .. }
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
    argument.validate(2).unwrap();
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
    argument.validate(0).unwrap();
    assert!(matches!(
        sentence(&argument, 0).validation.checks[0],
        StepCheck::Error { .. }
    ));
    assert!(matches!(
        sentence(&argument, 1).validation.checks[0],
        StepCheck::Unsat { .. }
    ));
    assert!(matches!(
        argument.root.validation.checks[0],
        StepCheck::Unsat { .. }
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
    argument.validate(0).unwrap();
    let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(matches!(goal.validation.checks[0], StepCheck::Unsat { .. }));
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
    argument.validate(2).unwrap();
    let ArgumentItem::Goal(goal) = &argument.root.steps[0] else {
        panic!("expected nested goal")
    };
    assert!(
        goal.validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Unsat { .. }))
    );
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
    argument.validate(0).unwrap();
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
    arguments.validate(0);
    assert!(arguments.0[0].error.is_some());
    assert!(arguments.0[1].error.is_none());
    assert!(!arguments.0[1].root.validation.checks.is_empty());
}
