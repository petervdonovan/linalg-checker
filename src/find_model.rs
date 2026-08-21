use std::fmt::{self, Display};

use markdown::mdast::{Heading, Node, Root};

pub use crate::model_finding::{ModelFindingError, ModelOrUnsat, NotSolvedYet, ToFromMd};
use crate::{
    Expr,
    enumerable_envspec::{
        ShapeError, extract_prepared_environment_iterator, infer_symbolic_type_environment,
    },
    model_finding::{
        expression_list, heading, heading_text, parse_expression_section, render_md, root,
        root_children, section_start, solve_prepared_environment,
    },
    preprocessing::prepare_expression,
    visit_mut::VisitContext,
};

#[derive(Debug, PartialEq, Eq)]
pub struct TestCase<Conclusion> {
    pub name: String,
    pub assumptions: Vec<Expr<()>>,
    pub sentences: Vec<Expr<()>>,
    pub conclusion: Conclusion,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TestCases<Conclusion>(pub Vec<TestCase<Conclusion>>);

macro_rules! impl_display {
    ($type:ty) => {
        impl Display for $type {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&render_md(&self.to_md()))
            }
        }
    };
}

impl_display!(TestCase<NotSolvedYet>);
impl_display!(TestCase<ModelOrUnsat>);
impl_display!(TestCases<NotSolvedYet>);
impl_display!(TestCases<ModelOrUnsat>);

impl<Conclusion: ToFromMd> ToFromMd for TestCase<Conclusion> {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        assert!(
            matches!(
                children.first(),
                Some(Node::Heading(Heading { depth: 1, .. }))
            ),
            "test case must start with a level-one heading"
        );
        let name = heading_text(&children[0]);
        let assumptions_start = section_start(children, "Assumptions");
        let sentences_start = section_start(children, "Sentences");
        let conclusion_start = section_start(children, "Conclusion");
        assert!(
            assumptions_start < sentences_start && sentences_start < conclusion_start,
            "test case sections are out of order"
        );
        let assumptions = parse_expression_section(
            &children[assumptions_start + 1..sentences_start],
            "assumptions",
        );
        let sentences = parse_expression_section(
            &children[sentences_start + 1..conclusion_start],
            "sentences",
        );
        let conclusion = Conclusion::parse_md(&Node::Root(Root {
            children: children[conclusion_start + 1..].to_vec(),
            position: None,
        }));
        Self {
            name,
            assumptions,
            sentences,
            conclusion,
        }
    }

    fn to_md(&self) -> Node {
        let mut children = vec![heading(1, &self.name), heading(2, "Assumptions")];
        if !self.assumptions.is_empty() {
            children.push(expression_list(&self.assumptions));
        }
        children.push(heading(2, "Sentences"));
        if !self.sentences.is_empty() {
            children.push(expression_list(&self.sentences));
        }
        children.push(heading(2, "Conclusion"));
        children.extend(root_children(&self.conclusion.to_md()).iter().cloned());
        root(children)
    }
}

impl<Conclusion: ToFromMd> ToFromMd for TestCases<Conclusion> {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        let starts: Vec<_> = children
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match node {
                Node::Heading(Heading { depth: 1, .. }) => Some(index),
                _ => None,
            })
            .collect();
        assert!(!starts.is_empty(), "test-case collection is empty");
        Self(
            starts
                .iter()
                .enumerate()
                .map(|(index, start)| {
                    let end = starts.get(index + 1).copied().unwrap_or(children.len());
                    TestCase::parse_md(&Node::Root(Root {
                        children: children[*start..end].to_vec(),
                        position: None,
                    }))
                })
                .collect(),
        )
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "test-case collection is empty");
        root(
            self.0
                .iter()
                .flat_map(|case| root_children(&case.to_md()).to_vec())
                .collect(),
        )
    }
}

impl TestCases<NotSolvedYet> {
    pub fn find_models(
        self,
        max_dimension: u64,
    ) -> Result<TestCases<ModelOrUnsat>, ModelFindingError> {
        Ok(TestCases(
            self.0
                .into_iter()
                .map(|test_case| test_case.find_model(max_dimension))
                .collect::<Result<_, _>>()?,
        ))
    }
}

impl TestCase<NotSolvedYet> {
    fn find_model(self, max_dimension: u64) -> Result<TestCase<ModelOrUnsat>, ModelFindingError> {
        let Self {
            name,
            assumptions,
            sentences,
            conclusion: NotSolvedYet,
        } = self;
        let symbolic_types = infer_symbolic_type_environment(&assumptions)?;
        let positive = VisitContext {
            logical_polarity: true,
        };
        let prepared_assumptions = assumptions
            .iter()
            .map(|expression| prepare_expression(&symbolic_types, expression, positive))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)?;
        let prepared_sentences = sentences
            .iter()
            .map(|expression| prepare_expression(&symbolic_types, expression, positive))
            .collect::<Result<Vec<_>, _>>()
            .map_err(crate::to_z3::ToZ3Error::from)?;
        let conclusion = match extract_prepared_environment_iterator(
            &symbolic_types,
            &prepared_assumptions,
            &prepared_sentences,
            max_dimension,
        ) {
            Err(ShapeError::Unsat(_)) => ModelOrUnsat::Unsat,
            Err(ShapeError::Unknown(_)) => ModelOrUnsat::Unknown,
            Err(error) => return Err(error.into()),
            Ok(environments) => {
                let dimension_bound_is_exhaustive = environments.dimension_bound_is_exhaustive();
                let mut conclusion = None;
                for environment in environments {
                    let environment = match environment {
                        Ok(environment) => environment,
                        Err(ShapeError::Unknown(_)) => {
                            conclusion = Some(ModelOrUnsat::Unknown);
                            break;
                        }
                        Err(error) => return Err(error.into()),
                    };
                    let prepared = prepared_assumptions
                        .iter()
                        .chain(prepared_sentences.iter())
                        .cloned()
                        .collect::<Vec<_>>();
                    match solve_prepared_environment(&environment, &prepared)? {
                        ModelOrUnsat::Unsat => {}
                        result @ (ModelOrUnsat::Model(_, _) | ModelOrUnsat::Unknown) => {
                            conclusion = Some(result);
                            break;
                        }
                        ModelOrUnsat::UnsatUpToDimension(_) => unreachable!(),
                    }
                }
                conclusion.unwrap_or({
                    if dimension_bound_is_exhaustive {
                        ModelOrUnsat::Unsat
                    } else {
                        ModelOrUnsat::UnsatUpToDimension(max_dimension)
                    }
                })
            }
        };
        Ok(TestCase {
            name,
            assumptions,
            sentences,
            conclusion,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{ModelOrUnsat, NotSolvedYet, TestCase, TestCases, ToFromMd};

    #[test]
    fn assumption_case_round_trips() {
        let input = r#"# Symbolic

## Assumptions

- $A \in \mathbb{R}^{n \times d + p}$

## Sentences

- $A = A$

## Conclusion

Not solved yet"#;
        let case = TestCase::<NotSolvedYet>::parse_str(input);
        assert_eq!(case.to_string(), input);
    }

    #[test]
    fn bounded_unsat_round_trips() {
        let input = r#"# Bounded

## Assumptions

- $A = A$

## Sentences

## Conclusion

Unsat up to dimension 4"#;
        let case = TestCase::<ModelOrUnsat>::parse_str(input);
        assert_eq!(case.to_string(), input);
    }

    #[test]
    fn invalid_sentence_dimensions_return_an_error() {
        let input = r#"# Invalid

## Assumptions

- $A \in \mathbb{R}^{2}$

## Sentences

- $A = \begin{bmatrix}1\end{bmatrix}$

## Conclusion

Not solved yet"#;
        let error = TestCases(vec![TestCase::<NotSolvedYet>::parse_str(input)])
            .find_models(2)
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "scalar-matrix comparisons are not supported"
        );
    }

    #[test]
    fn exhaustive_and_bounded_contradictions_have_distinct_conclusions() {
        let fixed = r#"# Fixed

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Sentences

- $A \ne A$

## Conclusion

Not solved yet"#;
        let symbolic = r#"# Symbolic

## Assumptions

- $A = A$

## Sentences

- $A \ne A$

## Conclusion

Not solved yet"#;
        let solved = TestCases(vec![
            TestCase::<NotSolvedYet>::parse_str(fixed),
            TestCase::<NotSolvedYet>::parse_str(symbolic),
        ])
        .find_models(2)
        .unwrap();

        assert_eq!(solved.0[0].conclusion, ModelOrUnsat::Unsat);
        assert_eq!(solved.0[1].conclusion, ModelOrUnsat::UnsatUpToDimension(2));
    }
}
