use linalg_sandbox::find_model::{ModelOrUnsat, NotSolvedYet, TestCases, ToFromMd};

const INPUT: &str = include_str!("fixtures/find_models_input.md");
const EXPECTED: &str = include_str!("fixtures/find_models_output.md");

fn without_final_newline(value: &str) -> &str {
    value.strip_suffix('\n').unwrap_or(value)
}

#[test]
fn find_model_fixtures_are_canonical_markdown() {
    let input = TestCases::<NotSolvedYet>::parse_str(INPUT);
    assert_eq!(input.to_string(), without_final_newline(INPUT));

    let expected = TestCases::<ModelOrUnsat>::parse_str(EXPECTED);
    assert_eq!(expected.to_string(), without_final_newline(EXPECTED));
}

/// Run with `cargo test --test find_model -- --ignored`.
#[test]
#[ignore = "model extraction from satisfiable Z3 results is not implemented"]
fn finds_models_matching_committed_markdown() {
    let input = TestCases::<NotSolvedYet>::parse_str(INPUT);
    let actual = input.find_models().to_string();
    assert_eq!(actual, without_final_newline(EXPECTED));
}
