use std::path::Path;

use linalg_sandbox::validate_argument::{
    Argument, Arguments, StepCheck, StepValidationData, ToFromMd,
};

const MAX_DIMENSION: u64 = 2;

fn without_final_newline(value: &str) -> &str {
    value.strip_suffix('\n').unwrap_or(value)
}

fn validate_corpus(name: &str) -> (Arguments, String) {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let input_path = manifest.join(format!("examples/validate_argument/{name}.md"));
    let fixture_path = manifest.join(format!("examples/validate_argument/{name}.output.md"));
    let input = std::fs::read_to_string(&input_path).expect("failed to read example corpus");
    let mut arguments = Arguments::parse_str(&input);
    let timings = arguments.validate(
        MAX_DIMENSION,
        &linalg_sandbox::timing::Timings::new("", MAX_DIMENSION),
    );
    std::fs::write(
        fixture_path.with_extension("timing.csv"),
        linalg_sandbox::timing::to_csv(timings).expect("failed to serialize timings"),
    )
    .expect("failed to write timings");
    let actual = arguments.to_string();

    if std::env::var_os("UPDATE_EXPECT").is_some() {
        std::fs::write(&fixture_path, format!("{actual}\n"))
            .expect("failed to update example fixture");
        return (arguments, actual);
    }

    let expected = std::fs::read_to_string(&fixture_path).expect("failed to read example fixture");
    assert_eq!(
        actual,
        without_final_newline(&expected),
        "rendered output differs for {name} at {} (actual {}, expected {})",
        fixture_path.display(),
        actual.len(),
        expected.len()
    );
    (arguments, actual)
}

fn has_success_check(validation: &StepValidationData) -> bool {
    validation.checks.iter().any(|check| {
        matches!(
            check,
            StepCheck::Unsat { .. }
                | StepCheck::Counterexample { .. }
                | StepCheck::ExistentialWitness { .. }
                | StepCheck::TacticEstablished
                | StepCheck::EstablishedByFact { .. }
        )
    })
}

fn argument_by_name<'a>(arguments: &'a Arguments, name: &str) -> &'a Argument {
    arguments
        .0
        .iter()
        .find(|argument| argument.name == name)
        .unwrap_or_else(|| panic!("missing example {name:?}"))
}

#[test]
fn success_examples_match_current_validation() {
    let (arguments, _) = validate_corpus("successes");
    assert!(arguments.0.len() >= 10);
    for argument in &arguments.0 {
        assert!(
            argument.error.is_none(),
            "success example failed: {}",
            argument.name
        );
        assert!(
            has_success_check(&argument.root.validation),
            "success example has no successful validation evidence: {}",
            argument.name
        );
    }
}

#[test]
fn failure_examples_match_current_validation() {
    let (arguments, output) = validate_corpus("failures");
    assert!(arguments.0.len() >= 10);
    let expected_markers = [
        (
            "The spectral norm of a wide matrix",
            "dimensionally invalid",
        ),
        (
            "The inverse identity for an invertible matrix",
            "unary operator remains",
        ),
        (
            "Nonnegativity of the Frobenius norm",
            "unary operator remains",
        ),
        (
            "A nested quantified statement under conjunction",
            "quantifiers embedded beneath another operator",
        ),
        (
            "A quantified premise needed to derive a concrete fact",
            "counterexample found",
        ),
        (
            "An existential witness requiring arithmetic reasoning",
            "no common syntactic witness was established",
        ),
        ("Zero-based sequence indexing", "✅ verified"),
        (
            "A flat induction proof without explicit obligations",
            "Unsupported step",
        ),
        (
            "The Gram matrix proof needs an explicitly introduced arbitrary vector",
            r"missing type for \vec{x}",
        ),
        (
            "A linear-independence definition with quantified coefficients",
            "## Error",
        ),
        (
            "A matrix square-root identity with unverified existence",
            "conditional",
        ),
        ("Componentwise ordering of vectors", "## Error"),
    ];
    for (name, marker) in expected_markers {
        let argument = argument_by_name(&arguments, name);
        assert!(
            output.contains(&format!("# {name}")),
            "failure example was not rendered: {name}"
        );
        assert!(
            argument.error.is_some()
                || argument.root.validation.checks.iter().any(|check| {
                    matches!(
                        check,
                        StepCheck::Counterexample { .. }
                            | StepCheck::Unknown { .. }
                            | StepCheck::DimensionallyInvalid { .. }
                            | StepCheck::Error { .. }
                            | StepCheck::QuantifierInconclusive { .. }
                            | StepCheck::MayBeUndefined { .. }
                            | StepCheck::AssumedExistence { .. }
                    )
                })
                || output.contains(marker),
            "failure example does not expose expected behavior: {name}"
        );
        assert!(
            output.contains(marker),
            "failure example changed diagnostic: {name}"
        );
    }
}
