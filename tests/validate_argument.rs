use linalg_sandbox::validate_argument::{
    ArgumentItem, Arguments, StepCheck, StepValidationData, ToFromMd,
};

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
