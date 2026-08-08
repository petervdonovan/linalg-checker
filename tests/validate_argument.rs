use linalg_sandbox::validate_argument::{Arguments, ToFromMd};

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
