use linalg_sandbox::find_model_given_environment::{
    ModelOrUnsat, NotSolvedYet, TestCases, ToFromMd,
};

const INPUT: &str = include_str!("fixtures/find_models_given_environment_input.md");
const EXPECTED: &str = include_str!("fixtures/find_models_given_environment_output.md");

fn without_final_newline(value: &str) -> &str {
    value.strip_suffix('\n').unwrap_or(value)
}

#[test]
fn find_model_given_environment_fixtures_are_canonical_markdown() {
    let input = TestCases::<NotSolvedYet>::parse_str(INPUT);
    assert_eq!(input.to_string(), without_final_newline(INPUT));

    let expected = TestCases::<ModelOrUnsat>::parse_str(EXPECTED);
    assert_eq!(expected.to_string(), without_final_newline(EXPECTED));
}

/// Run with `cargo test --test find_model_given_environment`.
///
/// Update the committed output with
/// `UPDATE_EXPECT=1 cargo test --test find_model_given_environment finds_models_matching_committed_markdown`.
#[test]
fn finds_models_matching_committed_markdown() {
    let input = TestCases::<NotSolvedYet>::parse_str(INPUT);
    let actual = input.find_models().unwrap().to_string();
    if std::env::var_os("UPDATE_EXPECT").is_some() {
        let output = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/find_models_given_environment_output.md");
        std::fs::write(output, format!("{actual}\n"))
            .expect("failed to update find_models_given_environment_output.md");
        return;
    }
    assert_eq!(actual, without_final_newline(EXPECTED));
}
