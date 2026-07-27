use std::fmt::{self, Display};

use markdown::{
    Constructs, ParseOptions,
    mdast::{Heading, InlineMath, List, ListItem, Node, Paragraph, Root, Text},
};

use crate::{Binop, Cmp, CmpChain, Environment, Expr, Model, RawExpr};

#[derive(Debug, PartialEq, Eq)]
pub struct TestCase<Conclusion> {
    pub name: String,
    pub sentences: Vec<Expr<()>>,
    pub environment: Environment,
    pub conclusion: Conclusion,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TestCases<Conclusion>(pub Vec<TestCase<Conclusion>>);

#[derive(Debug, PartialEq, Eq)]
pub struct NotSolvedYet;

#[derive(Debug, PartialEq, Eq)]
pub enum ModelOrUnsat {
    Unsat,
    Model(Model),
}

pub trait ToFromMd {
    fn parse_str(s: &str) -> Self
    where
        Self: Sized,
    {
        let options = ParseOptions {
            constructs: Constructs {
                math_text: true,
                math_flow: true,
                ..Constructs::default()
            },
            ..ParseOptions::default()
        };
        Self::parse_md(&markdown::to_mdast(s, &options).unwrap())
    }

    fn parse_md(md: &Node) -> Self;
    fn to_md(&self) -> Node;
}

macro_rules! impl_display {
    ($Tfm:ty) => {
        impl Display for $Tfm {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&render_md(&self.to_md()))
            }
        }
    };
}
impl_display!(TestCase<NotSolvedYet>);
impl_display!(ModelOrUnsat);
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
        let environment_start = section_start(children, "Environment");
        let sentences_start = section_start(children, "Sentences");
        let conclusion_start = section_start(children, "Conclusion");
        assert!(
            environment_start < sentences_start && sentences_start < conclusion_start,
            "test case sections are out of order"
        );

        let environment = parse_environment(&children[environment_start + 1..sentences_start]);
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
            sentences,
            environment,
            conclusion,
        }
    }

    fn to_md(&self) -> Node {
        let mut children = vec![heading(1, &self.name), heading(2, "Environment")];
        let environment = environment_expressions(&self.environment);
        if !environment.is_empty() {
            children.push(expression_list(&environment));
        }
        children.push(heading(2, "Sentences"));
        if !self.sentences.is_empty() {
            children.push(expression_list(&self.sentences));
        }
        children.push(heading(2, "Conclusion"));
        children.extend(root_children(&self.conclusion.to_md()).iter().cloned());
        Node::Root(Root {
            children,
            position: None,
        })
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

        let cases = starts
            .iter()
            .enumerate()
            .map(|(index, start)| {
                let end = starts.get(index + 1).copied().unwrap_or(children.len());
                TestCase::parse_md(&Node::Root(Root {
                    children: children[*start..end].to_vec(),
                    position: None,
                }))
            })
            .collect();
        Self(cases)
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "test-case collection is empty");
        Node::Root(Root {
            children: self
                .0
                .iter()
                .flat_map(|case| root_children(&case.to_md()).to_vec())
                .collect(),
            position: None,
        })
    }
}

impl ToFromMd for NotSolvedYet {
    fn parse_md(md: &Node) -> Self {
        assert_eq!(
            paragraph_text(single_root_child(md)),
            "Not solved yet",
            "expected an unsolved conclusion"
        );
        NotSolvedYet
    }

    fn to_md(&self) -> Node {
        root(vec![paragraph_text_node("Not solved yet")])
    }
}

impl ToFromMd for ModelOrUnsat {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        match children {
            [node] if paragraph_text(node) == "Unsat" => Self::Unsat,
            [label, list] if paragraph_text(label) == "Model" => {
                Self::Model(parse_expression_list(list))
            }
            _ => panic!("conclusion must be Unsat or Model followed by an expression list"),
        }
    }

    fn to_md(&self) -> Node {
        match self {
            Self::Unsat => root(vec![paragraph_text_node("Unsat")]),
            Self::Model(model) => {
                assert!(
                    !model.is_empty(),
                    "model must contain at least one expression"
                );
                root(vec![paragraph_text_node("Model"), expression_list(model)])
            }
        }
    }
}

fn environment_expressions(environment: &Environment) -> Vec<Expr<()>> {
    let mut expressions =
        Vec::with_capacity(environment.types.len() + environment.equalities.len());
    expressions.extend(environment.types.iter().map(|(variable, ty)| {
        Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(variable.clone())),
            Expr::new(RawExpr::Type(*ty)),
        ))
    }));
    expressions.extend(environment.equalities.iter().map(|(expression, value)| {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: expression.clone(),
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(*value)))],
        }))
    }));
    expressions.sort();
    expressions
}

fn parse_environment(nodes: &[Node]) -> Environment {
    if nodes.is_empty() {
        return Environment::default();
    }
    assert_eq!(
        nodes.len(),
        1,
        "environment must contain one expression list"
    );
    let mut environment = Environment::default();
    for expression in parse_expression_list(&nodes[0]) {
        match &expression.raw {
            RawExpr::Binop(Binop::ElementOf, left, right) => {
                let RawExpr::Variable(variable) = &left.raw else {
                    panic!("environment membership must have a variable on the left")
                };
                let RawExpr::Type(ty) = right.raw else {
                    panic!("environment membership must have a type on the right")
                };
                assert!(
                    environment.types.insert(variable.clone(), ty).is_none(),
                    "environment contains a duplicate type declaration"
                );
            }
            RawExpr::CmpChain(CmpChain { start, assertions })
                if matches!(
                    assertions.as_slice(),
                    [(Cmp::Eq, right)] if matches!(right.raw, RawExpr::NatLiteral(_))
                ) =>
            {
                let RawExpr::NatLiteral(value) = assertions[0].1.raw else {
                    unreachable!()
                };
                assert!(
                    environment
                        .equalities
                        .insert(start.clone(), value)
                        .is_none(),
                    "environment contains a duplicate equality"
                );
            }
            _ => panic!("expression does not have a valid environment-entry format"),
        }
    }
    environment
}

fn parse_expression_section(nodes: &[Node], name: &str) -> Vec<Expr<()>> {
    if nodes.is_empty() {
        Vec::new()
    } else {
        assert_eq!(nodes.len(), 1, "{name} must contain one expression list");
        parse_expression_list(&nodes[0])
    }
}

fn parse_expression_list(node: &Node) -> Vec<Expr<()>> {
    let Node::List(List {
        children,
        ordered: false,
        ..
    }) = node
    else {
        panic!("expected an unordered list of expressions")
    };
    children.iter().map(parse_expression_item).collect()
}

fn parse_expression_item(node: &Node) -> Expr<()> {
    let Node::ListItem(ListItem { children, .. }) = node else {
        panic!("expression list contains a non-list-item node")
    };
    let [Node::Paragraph(Paragraph { children, .. })] = children.as_slice() else {
        panic!("expression list item must contain one paragraph")
    };
    let [Node::InlineMath(InlineMath { value, .. })] = children.as_slice() else {
        panic!("expression list item must contain exactly one inline math expression")
    };
    let parsed = ratex_parser::parse(value).expect("invalid TeX in Markdown expression");
    crate::from_tex::expr(&parsed).expect("unsupported TeX in Markdown expression")
}

fn expression_list(expressions: &[Expr<()>]) -> Node {
    Node::List(List {
        children: expressions
            .iter()
            .map(|expression| {
                Node::ListItem(ListItem {
                    children: vec![Node::Paragraph(Paragraph {
                        children: vec![Node::InlineMath(InlineMath {
                            value: expression.as_latex().to_string(),
                            position: None,
                        })],
                        position: None,
                    })],
                    position: None,
                    spread: false,
                    checked: None,
                })
            })
            .collect(),
        position: None,
        ordered: false,
        start: None,
        spread: false,
    })
}

fn root(children: Vec<Node>) -> Node {
    Node::Root(Root {
        children,
        position: None,
    })
}

fn root_children(node: &Node) -> &[Node] {
    let Node::Root(Root { children, .. }) = node else {
        panic!("expected a Markdown root")
    };
    children
}

fn single_root_child(node: &Node) -> &Node {
    let [child] = root_children(node) else {
        panic!("expected exactly one Markdown block")
    };
    child
}

fn heading(depth: u8, value: &str) -> Node {
    Node::Heading(Heading {
        children: vec![text(value)],
        position: None,
        depth,
    })
}

fn heading_text(node: &Node) -> String {
    let Node::Heading(Heading { children, .. }) = node else {
        panic!("expected a heading")
    };
    inline_text(children)
}

fn section_start(nodes: &[Node], name: &str) -> usize {
    nodes
        .iter()
        .position(|node| {
            matches!(node, Node::Heading(Heading { depth: 2, .. })) && heading_text(node) == name
        })
        .unwrap_or_else(|| panic!("missing {name} section"))
}

fn paragraph_text_node(value: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![text(value)],
        position: None,
    })
}

fn paragraph_text(node: &Node) -> String {
    let Node::Paragraph(Paragraph { children, .. }) = node else {
        panic!("expected a paragraph")
    };
    inline_text(children)
}

fn inline_text(nodes: &[Node]) -> String {
    nodes
        .iter()
        .map(|node| match node {
            Node::Text(Text { value, .. }) => value.as_str(),
            _ => panic!("expected plain text"),
        })
        .collect()
}

fn text(value: &str) -> Node {
    Node::Text(Text {
        value: value.to_owned(),
        position: None,
    })
}

fn render_md(node: &Node) -> String {
    fn block(node: &Node) -> String {
        match node {
            Node::Heading(Heading {
                children, depth, ..
            }) => format!("{} {}", "#".repeat((*depth).into()), inline(children)),
            Node::Paragraph(Paragraph { children, .. }) => inline(children),
            Node::List(List {
                children,
                ordered: false,
                ..
            }) => children
                .iter()
                .map(|item| {
                    let Node::ListItem(ListItem { children, .. }) = item else {
                        panic!("list contains a non-list-item node")
                    };
                    let [Node::Paragraph(Paragraph { children, .. })] = children.as_slice() else {
                        panic!("list item must contain one paragraph")
                    };
                    format!("- {}", inline(children))
                })
                .collect::<Vec<_>>()
                .join("\n"),
            _ => panic!("unsupported Markdown block in canonical renderer"),
        }
    }

    fn inline(nodes: &[Node]) -> String {
        nodes
            .iter()
            .map(|node| match node {
                Node::Text(Text { value, .. }) => value.clone(),
                Node::InlineMath(InlineMath { value, .. }) => format!("${value}$"),
                _ => panic!("unsupported inline Markdown in canonical renderer"),
            })
            .collect()
    }

    root_children(node)
        .iter()
        .map(block)
        .collect::<Vec<_>>()
        .join("\n\n")
}

#[cfg(test)]
mod tests {
    use std::{
        collections::HashMap,
        fmt::{Debug, Display},
    };

    use expect_test::expect;

    use super::{ModelOrUnsat, NotSolvedYet, TestCase, TestCases, ToFromMd};
    use crate::{Cmp, CmpChain, Environment, Expr, RawExpr, Type, Variable};

    fn variable(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    fn equality(name: &str, value: u64) -> Expr<()> {
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: variable(name),
            assertions: vec![(Cmp::Eq, Expr::new(RawExpr::NatLiteral(value)))],
        }))
    }

    fn assert_stable<T>(input: &str) -> String
    where
        T: ToFromMd + Display + PartialEq + Debug,
    {
        let parsed = T::parse_str(input);
        let rendered = parsed.to_string();
        let reparsed = T::parse_str(&rendered);
        assert_eq!(parsed, reparsed);
        assert_eq!(rendered, reparsed.to_string());
        rendered
    }

    #[test]
    fn unsolved_case_round_trips_with_canonical_environment_order() {
        let input = r#"# Types

## Environment

- $k = 3$
- $x \in \mathbb{R}$
- $A \in \mathbb{R}^{2 \times 3}$
- $b \in \mathbb{B}$
- $n \in \mathbb{N}$
- $z \in \mathbb{Z}$

## Sentences

- $A \in \mathbb{R}^{2 \times 3}$
- $n = k$

## Conclusion

Not solved yet"#;

        expect![[r#"
            # Types

            ## Environment

            - $A \in \mathbb{R}^{2 \times 3}$
            - $b \in \mathbb{B}$
            - $n \in \mathbb{N}$
            - $x \in \mathbb{R}$
            - $z \in \mathbb{Z}$
            - $k = 3$

            ## Sentences

            - $A \in \mathbb{R}^{2 \times 3}$
            - $n = k$

            ## Conclusion

            Not solved yet"#]]
        .assert_eq(&assert_stable::<TestCase<NotSolvedYet>>(input));
    }

    #[test]
    fn model_and_unsat_cases_round_trip() {
        let unsat = r#"# Contradiction

## Environment

## Sentences

- $x = 1$

## Conclusion

Unsat"#;
        let model = r#"# Example

## Environment

- $x \in \mathbb{R}$

## Sentences

- $x = 2$

## Conclusion

Model

- $x = 2$
- $y = 3$"#;

        assert_eq!(assert_stable::<TestCase<ModelOrUnsat>>(unsat), unsat);
        assert_eq!(assert_stable::<TestCase<ModelOrUnsat>>(model), model);
    }

    #[test]
    fn collections_of_both_conclusion_families_round_trip() {
        let unsolved = r#"# First

## Environment

## Sentences

## Conclusion

Not solved yet

# Second

## Environment

- $n \in \mathbb{N}$

## Sentences

## Conclusion

Not solved yet"#;
        let solved = r#"# Unsat

## Environment

## Sentences

## Conclusion

Unsat

# Model

## Environment

## Sentences

## Conclusion

Model

- $x = 1$"#;

        assert_eq!(assert_stable::<TestCases<NotSolvedYet>>(unsolved), unsolved);
        assert_eq!(assert_stable::<TestCases<ModelOrUnsat>>(solved), solved);
    }

    #[test]
    fn programmatic_environment_rendering_is_deterministic() {
        let environment = Environment {
            types: HashMap::from([
                (Variable::new("x"), Type::Real),
                (Variable::new("A"), Type::Matrix(2, 3)),
                (Variable::new("b"), Type::Bool),
            ]),
            equalities: HashMap::from([(variable("k"), 3)]),
        };
        let case = TestCase {
            name: "Order".to_owned(),
            sentences: vec![equality("x", 1)],
            environment,
            conclusion: ModelOrUnsat::Unsat,
        };

        expect![[r#"
            # Order

            ## Environment

            - $A \in \mathbb{R}^{2 \times 3}$
            - $b \in \mathbb{B}$
            - $x \in \mathbb{R}$
            - $k = 3$

            ## Sentences

            - $x = 1$

            ## Conclusion

            Unsat"#]]
        .assert_eq(&case.to_string());
    }

    fn malformed_environment(entry: &str) {
        TestCase::<NotSolvedYet>::parse_str(&format!(
            "# Bad\n\n## Environment\n\n- ${entry}$\n\n## Sentences\n\n## Conclusion\n\nNot solved yet"
        ));
    }

    #[test]
    #[should_panic(expected = "environment membership must have a variable on the left")]
    fn environment_rejects_nonvariable_membership_subject() {
        malformed_environment(r"1 \in \mathbb{R}");
    }

    #[test]
    #[should_panic(expected = "environment membership must have a type on the right")]
    fn environment_rejects_nontype_membership_object() {
        malformed_environment(r"x \in A");
    }

    #[test]
    #[should_panic(expected = "environment membership must have a variable on the left")]
    fn environment_rejects_reversed_membership() {
        malformed_environment(r"\mathbb{R} \in x");
    }

    #[test]
    fn one_by_one_matrix_environment_type_canonicalizes_to_real() {
        let case = TestCase {
            name: "Canonical".to_owned(),
            sentences: Vec::new(),
            environment: Environment {
                types: HashMap::from([(Variable::new("A"), Type::Matrix(1, 1))]),
                equalities: HashMap::new(),
            },
            conclusion: NotSolvedYet,
        };
        let parsed = TestCase::<NotSolvedYet>::parse_str(&case.to_string());
        assert_eq!(parsed.environment.types[&Variable::new("A")], Type::Real);
    }
}
