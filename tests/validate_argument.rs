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
    arguments.validate(MAX_DIMENSION);
    let actual = arguments.to_string();
    if std::env::var_os("UPDATE_EXPECT").is_some() {
        let output = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/validate_arguments_output.md");
        std::fs::write(output, format!("{actual}\n"))
            .expect("failed to update validate_arguments_output.md");
        return;
    }
    assert_eq!(actual, without_final_newline(EXPECTED));
}

fn is_verified(validation: &StepValidationData) -> bool {
    !validation.checks.is_empty()
        && validation
            .checks
            .iter()
            .all(|check| matches!(check, StepCheck::Unsat { .. }))
}

#[test]
fn validates_nested_proof_of_monotone_squaring() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION);
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
    arguments.validate(MAX_DIMENSION);
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
    assert!(!argument.root.validation.environments_exhaustive);
    assert_eq!(argument.root.steps.len(), 2);
    for item in &argument.root.steps {
        let ArgumentItem::Goal(goal) = item else {
            panic!("induction obligations must be direct child goals")
        };
        assert!(
            goal.validation
                .checks
                .iter()
                .any(|check| matches!(check, StepCheck::Unsat { .. }))
        );
    }
}

#[test]
fn validates_scoped_vector_induction_from_dimension_one() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION);
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
    assert!(!argument.root.validation.environments_exhaustive);
    let [ArgumentItem::Goal(base), ArgumentItem::Goal(step)] = argument.root.steps.as_slice()
    else {
        panic!("expected direct base and successor goals")
    };
    assert!(is_verified(&base.validation));
    assert!(is_verified(&step.validation));
    assert_eq!(
        base.givens[0].as_latex().to_string(),
        r"x \in \mathbb{R}^{1}"
    );
    assert!(matches!(
        &step.givens[0].raw,
        RawExpr::Finop(Finop::Forall, expressions) if expressions.len() == 2
    ));
}

#[test]
fn validates_quantified_steps_and_goal_evidence() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION);

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
            .any(|check| matches!(check, StepCheck::EstablishedByFact { .. }))
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
            .any(witness_is_b)
    );
    let ArgumentItem::Sentence(existential) = &inferred_dimensions.root.steps[1] else {
        panic!("expected existential sentence")
    };
    assert!(existential.validation.checks.iter().any(witness_is_b));
}

#[test]
fn validates_determinant_of_a_diagonal_sequence() {
    let mut arguments = Arguments::parse_str(INPUT);
    arguments.validate(MAX_DIMENSION);
    let argument = arguments
        .0
        .iter()
        .find(|argument| argument.name == "Determinant of a diagonal matrix")
        .expect("missing diagonal determinant argument");

    assert!(argument.error.is_none());
    assert!(is_verified(&argument.root.validation));
    assert!(!argument.root.validation.environments_exhaustive);
}
