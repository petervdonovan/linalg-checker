//! Markdown-backed fixtures for collection-level expression rewrites.

use std::fmt::{self, Display};

use markdown::mdast::{Heading, Node, Paragraph, Root, Text};

pub use crate::model_finding::ToFromMd;

use crate::{
    Expr,
    model_finding::{
        expression_list, heading, heading_text, parse_expression_section, render_md, root,
        root_children, section_start,
    },
};

#[derive(Debug, PartialEq, Eq)]
pub struct RewriteCase {
    pub name: String,
    pub input: Vec<Expr<()>>,
    pub output: Option<Vec<Expr<()>>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RewriteCases(pub Vec<RewriteCase>);

impl RewriteCases {
    pub fn rewrite(self, mut rewrite: impl FnMut(&[Expr<()>]) -> Vec<Expr<()>>) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|case| RewriteCase {
                    output: Some(rewrite(&case.input)),
                    ..case
                })
                .collect(),
        )
    }

    pub fn try_rewrite<RewriteError>(
        self,
        mut rewrite: impl FnMut(&[Expr<()>]) -> Result<Vec<Expr<()>>, RewriteError>,
    ) -> Result<Self, RewriteError> {
        Ok(Self(
            self.0
                .into_iter()
                .map(|case| {
                    Ok(RewriteCase {
                        output: Some(rewrite(&case.input)?),
                        ..case
                    })
                })
                .collect::<Result<_, RewriteError>>()?,
        ))
    }
}

impl ToFromMd for RewriteCase {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        assert!(
            matches!(
                children.first(),
                Some(Node::Heading(Heading { depth: 1, .. }))
            ),
            "rewrite case must start with a level-one heading"
        );
        let name = heading_text(&children[0]);
        let input_start = section_start(children, "Input");
        let output_start = section_start(children, "Output");
        assert!(
            input_start < output_start,
            "rewrite case sections are out of order"
        );
        let input = parse_expression_section(&children[input_start + 1..output_start], "Input");
        assert!(
            !input.is_empty(),
            "Input must contain at least one expression"
        );
        let output = parse_optional_expression_list(&children[output_start + 1..]);
        Self {
            name,
            input,
            output,
        }
    }

    fn to_md(&self) -> Node {
        assert!(!self.input.is_empty(), "Input must not be empty");
        let mut children = vec![
            heading(1, &self.name),
            heading(2, "Input"),
            expression_list(&self.input),
        ];
        children.push(heading(2, "Output"));
        children.push(match &self.output {
            Some(expressions) => {
                assert!(!expressions.is_empty(), "Output must not be empty");
                expression_list(expressions)
            }
            None => text_paragraph("none"),
        });
        root(children)
    }
}

impl ToFromMd for RewriteCases {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        let starts = children
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match node {
                Node::Heading(Heading { depth: 1, .. }) => Some(index),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!starts.is_empty(), "rewrite-case collection is empty");
        Self(
            starts
                .iter()
                .enumerate()
                .map(|(index, start)| {
                    let end = starts.get(index + 1).copied().unwrap_or(children.len());
                    RewriteCase::parse_md(&Node::Root(Root {
                        children: children[*start..end].to_vec(),
                        position: None,
                    }))
                })
                .collect(),
        )
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "rewrite-case collection is empty");
        root(
            self.0
                .iter()
                .flat_map(|case| root_children(&case.to_md()).to_vec())
                .collect(),
        )
    }
}

impl Display for RewriteCase {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render_md(&self.to_md()))
    }
}

impl Display for RewriteCases {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render_md(&self.to_md()))
    }
}

fn parse_optional_expression_list(nodes: &[Node]) -> Option<Vec<Expr<()>>> {
    match nodes {
        [Node::Paragraph(Paragraph { children, .. })] if matches!(children.as_slice(), [Node::Text(Text { value, .. })] if value == "none") => {
            None
        }
        _ => {
            let expressions = parse_expression_section(nodes, "Output");
            assert!(
                !expressions.is_empty(),
                "Output must contain at least one expression"
            );
            Some(expressions)
        }
    }
}

fn text_paragraph(value: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![Node::Text(Text {
            value: value.to_owned(),
            position: None,
        })],
        position: None,
    })
}

#[cfg(test)]
mod tests {
    use super::{RewriteCases, ToFromMd};
    use crate::{Expr, RawExpr};

    #[test]
    fn rewrite_receives_and_replaces_the_complete_input_collection() {
        let cases = RewriteCases::parse_str(
            r"# Rewrite

## Input

- $n \in \mathbb{N}$
- $\ldots$

## Output

none",
        );
        let rewritten = cases.rewrite(|expressions| {
            assert_eq!(expressions.len(), 2);
            assert!(matches!(expressions[1].raw, RawExpr::Ellipsis));
            vec![Expr::new(RawExpr::NatLiteral(4))]
        });
        assert!(matches!(
            rewritten.0[0].output.as_ref().unwrap().as_slice(),
            [expression] if matches!(expression.raw, RawExpr::NatLiteral(4))
        ));
        assert_eq!(rewritten.0[0].input.len(), 2);
    }
}
