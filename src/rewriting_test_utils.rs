//! Markdown-backed fixtures for environment-specific expression rewrites.

use std::fmt::{self, Display};

use markdown::mdast::{Heading, InlineMath, Node, Paragraph, Root, Text};

pub use crate::model_finding::{ModelFindingError, ToFromMd};

use crate::{
    Environment, Expr,
    model_finding::{
        assignment_from_declarations, expression_list, heading, heading_text,
        parse_expression_section, render_md, root, root_children, section_start,
        validate_environment_entries,
    },
};

#[derive(Debug, PartialEq, Eq)]
pub struct RewriteCase {
    pub name: String,
    pub environment: Vec<Expr<()>>,
    pub input_expression: Expr<()>,
    pub output_expression: Option<Expr<()>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RewriteCases(pub Vec<RewriteCase>);

impl RewriteCases {
    pub fn rewrite(
        self,
        mut rewrite: impl FnMut(&Environment, &Expr<()>) -> Expr<()>,
    ) -> Result<Self, ModelFindingError> {
        self.try_rewrite(|environment, expression| Ok(rewrite(environment, expression)))
    }

    pub fn try_rewrite<RewriteError: From<ModelFindingError>>(
        self,
        mut rewrite: impl FnMut(&Environment, &Expr<()>) -> Result<Expr<()>, RewriteError>,
    ) -> Result<Self, RewriteError> {
        Ok(Self(
            self.0
                .into_iter()
                .map(|case| {
                    let environment = assignment_from_declarations(&case.environment)?;
                    Ok(RewriteCase {
                        output_expression: Some(rewrite(&environment, &case.input_expression)?),
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
        let environment_start = section_start(children, "Environment");
        let input_start = section_start(children, "Input");
        let output_start = section_start(children, "Output");
        assert!(
            environment_start < input_start && input_start < output_start,
            "rewrite case sections are out of order"
        );
        let mut environment =
            parse_expression_section(&children[environment_start + 1..input_start], "environment");
        validate_environment_entries(&environment);
        environment.sort();
        let input_expression = parse_expression(&children[input_start + 1..output_start]);
        let output_expression = parse_optional_expression(&children[output_start + 1..]);
        Self {
            name,
            environment,
            input_expression,
            output_expression,
        }
    }

    fn to_md(&self) -> Node {
        let mut environment = self.environment.clone();
        environment.sort();
        let mut children = vec![heading(1, &self.name), heading(2, "Environment")];
        if !environment.is_empty() {
            children.push(expression_list(&environment));
        }
        children.push(heading(2, "Input"));
        children.push(expression_paragraph(&self.input_expression));
        children.push(heading(2, "Output"));
        children.push(match &self.output_expression {
            Some(expression) => expression_paragraph(expression),
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

fn parse_expression(nodes: &[Node]) -> Expr<()> {
    let [Node::Paragraph(Paragraph { children, .. })] = nodes else {
        panic!("Expression must contain exactly one paragraph")
    };
    let [Node::InlineMath(InlineMath { value, .. })] = children.as_slice() else {
        panic!("Expression must contain exactly one inline math expression")
    };
    let parsed = ratex_parser::parse(value).expect("invalid TeX in rewrite expression");
    crate::from_tex::expr(&parsed).expect("unsupported TeX in rewrite expression")
}

fn expression_paragraph(expression: &Expr<()>) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![Node::InlineMath(InlineMath {
            value: expression.as_latex().to_string(),
            position: None,
        })],
        position: None,
    })
}

fn parse_optional_expression(nodes: &[Node]) -> Option<Expr<()>> {
    let [Node::Paragraph(Paragraph { children, .. })] = nodes else {
        panic!("Output must contain exactly one paragraph")
    };
    match children.as_slice() {
        [Node::Text(Text { value, .. })] if value == "none" => None,
        [Node::InlineMath(InlineMath { value, .. })] => {
            let parsed = ratex_parser::parse(value).expect("invalid TeX in rewrite output");
            Some(crate::from_tex::expr(&parsed).expect("unsupported TeX in rewrite output"))
        }
        _ => panic!("Output must be `none` or one inline math expression"),
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
    use crate::{Expr, NaturalParameter, RawExpr, Variable};

    #[test]
    fn rewrite_receives_the_concrete_environment_and_replaces_the_expression() {
        let cases = RewriteCases::parse_str(
            r"# Rewrite

## Environment

- $n \in \mathbb{N}$
- $n = 4$

## Input

$\ldots$

## Output

none",
        );
        let rewritten = cases
            .rewrite(|environment, expression| {
                assert!(matches!(expression.raw, RawExpr::Ellipsis));
                let value =
                    environment.natural_assignment[&NaturalParameter::Variable(Variable::new("n"))];
                Expr::new(RawExpr::NatLiteral(value))
            })
            .unwrap();
        assert!(matches!(
            rewritten.0[0].output_expression.as_ref().unwrap().raw,
            RawExpr::NatLiteral(4)
        ));
        assert!(matches!(
            rewritten.0[0].input_expression.raw,
            RawExpr::Ellipsis
        ));
    }
}
