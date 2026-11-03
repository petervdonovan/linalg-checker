use linalg_sandbox::validate_argument::{
    ArgumentItem, Arguments, StepCheck, StepValidationData, ToFromMd,
};
use linalg_sandbox::{Finop, RawExpr};

const MAX_DIMENSION: u64 = 2;
const INPUT: &str = include_str!("fixtures/validate_arguments_input.md");
const EXPECTED: &str = include_str!("fixtures/validate_arguments_output.md");

fn without_final_newline(value: &str) -> &str {
    value.strip_suffix('\n').unwrap_or(value)
}

#[test]
fn argument_input_is_canonical_markdown() {
    let input = Arguments::parse_str(INPUT);
    assert_eq!(input.to_string(), without_final_newline(INPUT));
}

#[test]
fn validates_arguments_matching_committed_markdown() {
    let mut arguments = Arguments::parse_str(INPUT);
    let timings = arguments.validate(
        MAX_DIMENSION,
        &linalg_sandbox::timing::Timings::new("", MAX_DIMENSION),
    );
    let output = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/validate_arguments_output.md");
    std::fs::write(
        output.with_extension("timing.csv"),
        linalg_sandbox::timing::to_csv(timings).expect("failed to serialize timings"),
    )
    .expect("failed to write timings");
    let actual = arguments.to_string();
    if std::env::var_os("UPDATE_EXPECT").is_some() {
        std::fs::write(output, format!("{actual}\n"))
            .expect("failed to update validate_arguments_output.md");
        return;
    }
    assert_eq!(actual, without_final_newline(EXPECTED));
}

fn is_verified(validation: &StepValidationData) -> bool {
    !validation.checks.is_empty()
        && validation.checks.iter().all(|check| {
            matches!(
                check,
                StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
            )
        })
}

#[test]
fn validates_nested_proof_of_monotone_squaring() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default());
    let argument = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Squaring nonnegative reals")
        .expect("missing nested squaring argument");

    assert!(argument.error.is_none());
    assert!(is_verified(&argument.root.validation));
    assert_eq!(argument.root.steps.len(), 5);
    let ArgumentItem::Goal(subgoal) = &argument.root.steps[0] else {
        panic!("first proof item should be a nested goal")
    };
    assert!(is_verified(&subgoal.validation));
    assert_eq!(subgoal.steps.len(), 2);
    for item in subgoal.steps.iter().chain(&argument.root.steps[1..]) {
        let ArgumentItem::Sentence(step) = item else {
            panic!("expected an ordinary proof sentence")
        };
        assert!(is_verified(&step.validation));
    }

    let rendered = argument.to_string();
    let wts = rendered.find("1. WTS $0 \\le y$").unwrap();
    let details = rendered[wts..].find("   <details>").unwrap() + wts;
    let body = rendered[wts..].find("   1. $x \\le y$").unwrap() + wts;
    assert!(wts < details && details < body);
}

#[test]
fn validates_nested_induction_obligations() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default());
    let argument = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Powers of two by induction")
        .expect("missing induction argument");

    assert!(argument.error.is_none());
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::TacticEstablished))
    );
    assert!(argument.root.validation.environments_exhaustive);
    assert_eq!(argument.root.steps.len(), 2);
    for item in &argument.root.steps {
        let ArgumentItem::Goal(goal) = item else {
            panic!("induction obligations must be direct child goals")
        };
        assert!(goal.validation.checks.iter().any(|check| matches!(
            check,
            StepCheck::Unsat { .. } | StepCheck::NaturalDeduction { .. }
        )));
    }
}

#[test]
fn validates_scoped_vector_induction_from_dimension_one() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default());
    let argument = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Squared norm in every dimension")
        .expect("missing vector induction argument");

    assert!(argument.error.is_none());
    assert!(
        argument
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::TacticEstablished))
    );
    assert!(argument.root.validation.environments_exhaustive);
    let [ArgumentItem::Goal(base), ArgumentItem::Goal(step)] = argument.root.steps.as_slice()
    else {
        panic!("expected direct base and successor goals")
    };
    assert!(is_verified(&base.validation));
    assert!(is_verified(&step.validation));
    assert_eq!(
        base.givens[0].as_latex().to_string(),
        r"\vec{x} \in \mathbb{R}^{1}"
    );
    assert!(matches!(
        &step.givens[0].raw,
        RawExpr::Finop(Finop::Forall, expressions) if expressions.len() == 2
    ));
}

#[test]
fn validates_quantified_steps_and_goal_evidence() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default());

    let quantified = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Quantified claims as ordinary steps")
        .expect("missing quantified-step argument");
    let ArgumentItem::Sentence(existential) = &quantified.root.steps[0] else {
        panic!("expected existential sentence")
    };
    assert!(existential.validation.checks.iter().any(|check| matches!(
        check,
        StepCheck::ExistentialWitness { assignments, .. }
            if assignments.iter().any(|(variable, value)|
                variable.name == "z" && value.as_latex().to_string() == "1")
    )));
    assert!(
        quantified
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(
                check,
                StepCheck::NaturalDeduction {
                    proof: linalg_sandbox::natural_deduction::NaturalDeductionProof::Reuse { .. },
                    ..
                }
            ))
    );

    let direct = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Existential evidence from direct subgoals")
        .expect("missing direct-evidence argument");
    assert!(
        direct
            .root
            .validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    );

    let inferred_dimensions = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Existential involving inferred dimensions")
        .expect("missing inferred-dimension existential argument");
    let witness_is_b = |check: &StepCheck| {
        matches!(
            check,
            StepCheck::ExistentialWitness { assignments, .. }
                if assignments.iter().any(|(variable, value)|
                    variable.name == "C"
                        && matches!(&value.raw, RawExpr::Variable(value) if value.name == "B"))
        )
    };
    assert!(
        inferred_dimensions
            .root
            .validation
            .checks
            .iter()
            .any(|check| witness_is_b(check)
                || matches!(
                    check,
                    StepCheck::NaturalDeduction {
                        proof: linalg_sandbox::natural_deduction::NaturalDeductionProof::Reuse { .. },
                        ..
                    }
                ))
    );
    let ArgumentItem::Sentence(existential) = &inferred_dimensions.root.steps[1] else {
        panic!("expected existential sentence")
    };
    assert!(existential.validation.checks.iter().any(witness_is_b));
}

#[test]
fn validates_determinant_of_a_diagonal_sequence() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default());
    let argument = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Determinant of a diagonal matrix")
        .expect("missing diagonal determinant argument");

    assert!(argument.error.is_none());
    assert!(is_verified(&argument.root.validation));
    assert!(!argument.root.validation.environments_exhaustive);
}

fn validate_fixture(name: &str) -> linalg_sandbox::validate_argument::Argument {
    let mut argument = Arguments::parse_str(INPUT)
        .0
        .into_iter()
        .find(|argument| argument.name == name)
        .expect("missing natural-deduction fixture");
    argument
        .validate(MAX_DIMENSION, &linalg_sandbox::timing::Timings::default())
        .unwrap();
    assert!(argument.error.is_none());
    argument
}

fn child(
    goal: &linalg_sandbox::validate_argument::Goal,
    index: usize,
) -> &linalg_sandbox::validate_argument::Goal {
    let ArgumentItem::Goal(child) = &goal.steps[index] else {
        panic!("expected nested goal");
    };
    child
}

fn sentence(
    goal: &linalg_sandbox::validate_argument::Goal,
    index: usize,
) -> &linalg_sandbox::validate_argument::ArgumentStep {
    let ArgumentItem::Sentence(step) = &goal.steps[index] else {
        panic!("expected ordinary sentence");
    };
    step
}

fn deduction(
    validation: &StepValidationData,
) -> &linalg_sandbox::natural_deduction::NaturalDeductionProof {
    let [StepCheck::NaturalDeduction { proof, .. }] = validation.checks.as_slice() else {
        panic!("expected a single deduction proof, got {validation:?}");
    };
    assert!(validation.environments_exhaustive);
    proof
}

fn assert_counterexample(validation: &StepValidationData) {
    assert!(
        validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::Counterexample { .. })),
        "{validation:?}"
    );
    assert!(
        !validation
            .checks
            .iter()
            .any(|check| matches!(check, StepCheck::NaturalDeduction { .. })),
        "{validation:?}"
    );
}

fn assert_undefined_a(validation: &StepValidationData) {
    assert!(
        matches!(validation.checks.as_slice(), [StepCheck::Error { error, .. }] if error.to_string() == "reference to undefined variable $a$"),
        "{validation:?}"
    );
}

fn assert_descendant_witness(
    validation: &StepValidationData,
    inner: &linalg_sandbox::validate_argument::Goal,
) {
    let [
        StepCheck::ExistentialWitness {
            assignments,
            supporting_facts,
        },
    ] = validation.checks.as_slice()
    else {
        panic!("expected existential evidence from descendants, got {validation:?}");
    };
    assert_eq!(assignments.len(), 1);
    assert_eq!(assignments[0].0.name, "x");
    assert_eq!(assignments[0].1.as_latex().to_string(), "1");
    assert_eq!(supporting_facts.len(), 2);
    for i in 0..2 {
        assert!(is_verified(&sentence(inner, i).validation));
        assert!(supporting_facts.contains(&sentence(inner, i).sentence));
    }
}

#[test]
fn independent_descendants_cross_multiple_scope_boundaries() {
    use linalg_sandbox::natural_deduction::NaturalDeductionProof;
    let argument = validate_fixture("Independent facts cross multiple block boundaries");
    let outer = child(&argument.root, 0);
    let inner = child(outer, 0);
    assert!(is_verified(&outer.validation));
    assert!(is_verified(&inner.validation));
    assert_descendant_witness(&argument.root.validation, inner);
    let NaturalDeductionProof::Reuse { premise, exact } =
        deduction(&sentence(&argument.root, 1).validation)
    else {
        panic!("the parent must reuse the exported descendant");
    };
    assert!(*exact);
    assert_eq!(premise.expression, sentence(inner, 2).sentence);
}

#[test]
fn failed_goals_export_successful_descendants_without_admitting_the_failed_claim() {
    let argument = validate_fixture("Independent facts survive a failed goal");
    let failed = child(&argument.root, 0);
    assert_counterexample(&failed.validation);
    assert_descendant_witness(&argument.root.validation, failed);
    assert_counterexample(&sentence(&argument.root, 1).validation);
}

#[test]
fn explicit_implication_introduction_exports_only_the_discharged_fact() {
    use linalg_sandbox::natural_deduction::NaturalDeductionProof;
    let argument = validate_fixture("Explicit implication introduction exports a discharged fact");
    let block = child(&argument.root, 0);
    assert!(is_verified(&sentence(block, 0).validation));
    assert_counterexample(&block.validation);
    let NaturalDeductionProof::ImplicationIntroduction {
        premise,
        discharged,
    } = deduction(&sentence(block, 1).validation)
    else {
        panic!("ordinary sentence must use implication introduction");
    };
    assert_eq!(premise.expression, block.givens[0]);
    assert_eq!(discharged.len(), 1);
    for validation in [
        &sentence(&argument.root, 1).validation,
        &argument.root.validation,
    ] {
        assert!(
            matches!(deduction(validation), NaturalDeductionProof::Reuse { premise, exact: true } if premise.expression == sentence(block, 1).sentence),
            "expected exported fact reuse, got {:?}",
            deduction(validation)
        );
    }
    assert_counterexample(&sentence(&argument.root, 2).validation);
}

#[test]
fn explicit_universal_introduction_exports_a_fact_available_for_instantiation() {
    use linalg_sandbox::natural_deduction::NaturalDeductionProof;
    let argument = validate_fixture("Explicit universal introduction exports a quantified fact");
    let block = child(&argument.root, 0);
    assert!(is_verified(&block.validation));
    assert!(is_verified(&sentence(block, 0).validation));
    let NaturalDeductionProof::UniversalIntroduction {
        premise,
        assignments,
        discharged,
    } = deduction(&sentence(block, 1).validation)
    else {
        panic!("ordinary sentence must use universal introduction");
    };
    assert_eq!(premise.expression, sentence(block, 0).sentence);
    assert_eq!(assignments.len(), 1);
    assert_eq!(assignments[&linalg_sandbox::Variable::new("t")].name, "a");
    assert_eq!(discharged.len(), 1);
    assert!(
        matches!(deduction(&sentence(&argument.root, 1).validation), NaturalDeductionProof::Reuse { premise, exact: true } if premise.expression == sentence(block, 1).sentence)
    );
    // After instantiation, generalizing b discharges the remaining parent
    // declaration and gives the final goal a proof with fewer dependencies.
    let NaturalDeductionProof::UniversalIntroduction {
        premise,
        assignments,
        discharged,
    } = deduction(&argument.root.validation)
    else {
        panic!("final goal must generalize the established parent instance");
    };
    assert_eq!(premise.expression, sentence(&argument.root, 2).sentence);
    assert_eq!(assignments.len(), 1);
    assert_eq!(assignments[&linalg_sandbox::Variable::new("t")].name, "b");
    assert_eq!(discharged.len(), 1);
    let NaturalDeductionProof::UniversalElimination {
        source,
        assignments,
        ..
    } = deduction(&sentence(&argument.root, 2).validation)
    else {
        panic!("parent must instantiate the exported universal");
    };
    assert_eq!(source.expression, sentence(block, 1).sentence);
    assert_eq!(assignments.len(), 1);
    assert!(
        matches!(&assignments[&linalg_sandbox::Variable::new("t")].raw, RawExpr::Variable(v) if v.name == "b")
    );
    assert_undefined_a(&sentence(&argument.root, 3).validation);
}

#[test]
fn universal_introduction_cannot_discharge_a_remaining_restriction() {
    let argument = validate_fixture("Remaining assumptions prevent universal introduction");
    let block = child(&argument.root, 0);
    assert!(is_verified(&block.validation));
    assert_counterexample(&sentence(block, 0).validation);
    assert_counterexample(&sentence(&argument.root, 1).validation);
    assert_counterexample(&argument.root.validation);
}

#[test]
fn witnesses_remain_local_and_are_not_arbitrary_parameters() {
    let argument = validate_fixture("Local existential witnesses cannot be generalized");
    let block = child(&argument.root, 0);
    assert!(
        matches!(sentence(block, 0).validation.checks.as_slice(), [StepCheck::ExistentialElimination { fact, assignments }] if fact == &argument.root.givens[0] && assignments.len() == 1 && assignments[0].0.name == "x" && assignments[0].1.name == "a")
    );
    assert!(is_verified(&block.validation));
    assert_counterexample(&sentence(block, 1).validation);
    assert_undefined_a(&sentence(&argument.root, 1).validation);
    assert_counterexample(&argument.root.validation);
}
