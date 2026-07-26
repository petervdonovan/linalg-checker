use std::fmt::Display;

use crate::{Environment, Expr};

pub struct TestCase {
    pub name: String,
    pub sentences: Vec<Expr<()>>,
    pub environment: Environment,
}
pub struct TestCases(pub Vec<TestCase>);

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!(
            "return valid markdown. Embedded latex using $...$ is the ideal way to represent math"
        )
    }
}
impl Display for TestCases {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!(
            "return valid markdown. Embedded latex using $...$ is the ideal way to represent math"
        )
    }
}
