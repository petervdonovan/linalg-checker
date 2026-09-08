use linalg_sandbox::{
    ellipsis_elimination::eliminate_ellipses,
    rewriting_test_utils::{RewriteCases, ToFromMd},
};

const INPUT: &str = include_str!("fixtures/ellipsis_elimination_input.md");
const EXPECTED: &str = include_str!("fixtures/ellipsis_elimination_output.md");

fn without_final_newline(value: &str) -> &str {
    value.strip_suffix('\n').unwrap_or(value)
}

#[test]
fn ellipsis_elimination_fixtures_are_canonical_markdown() {
    let input = RewriteCases::parse_str(INPUT);
    assert_eq!(input.to_string(), without_final_newline(INPUT));

    let expected = RewriteCases::parse_str(EXPECTED);
    assert_eq!(expected.to_string(), without_final_newline(EXPECTED));
}

/// Update with
/// `UPDATE_EXPECT=1 cargo test --test ellipsis_elimination rewrites_ellipsis_fixtures`.
#[test]
fn rewrites_ellipsis_fixtures() {
    let actual = RewriteCases::parse_str(INPUT)
        .rewrite(eliminate_ellipses)
        .unwrap()
        .to_string();
    if std::env::var_os("UPDATE_EXPECT").is_some() {
        let output = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/ellipsis_elimination_output.md");
        std::fs::write(output, format!("{actual}\n"))
            .expect("failed to update ellipsis-elimination output");
        return;
    }
    assert_eq!(actual, without_final_newline(EXPECTED));
}
