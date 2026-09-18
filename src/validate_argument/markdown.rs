use super::*;
use ::markdown::mdast::{Heading, Html, InlineMath, List, ListItem, Node, Paragraph, Root};

impl ToFromMd for Argument {
    fn parse_md(md: &Node) -> Self {
        let children = root_children(md);
        assert!(
            matches!(
                children.first(),
                Some(Node::Heading(Heading { depth: 1, .. }))
            ),
            "argument must start with a level-one heading"
        );
        let name = heading_text(&children[0]);
        let root = parse_goal(&children[1..]);
        Self {
            name,
            root,
            error: None,
        }
    }

    fn to_md(&self) -> Node {
        let expressions = argument_expressions(self);
        let mut children = vec![heading(1, &self.name)];
        children.extend(goal_nodes(&self.root, &expressions));
        if let Some(error) = &self.error {
            children.push(heading(2, "Error"));
            children.push(Node::Paragraph(Paragraph {
                children: vec![Node::Text(::markdown::mdast::Text {
                    value: error.to_string(),
                    position: None,
                })],
                position: None,
            }));
        }
        root(children)
    }
}

impl ToFromMd for Arguments {
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
        assert!(!starts.is_empty(), "argument collection is empty");
        Self(
            starts
                .iter()
                .enumerate()
                .map(|(index, start)| {
                    let end = starts.get(index + 1).copied().unwrap_or(children.len());
                    Argument::parse_md(&Node::Root(Root {
                        children: children[*start..end].to_vec(),
                        position: None,
                    }))
                })
                .collect(),
        )
    }

    fn to_md(&self) -> Node {
        assert!(!self.0.is_empty(), "argument collection is empty");
        root(
            self.0
                .iter()
                .flat_map(|argument| root_children(&argument.to_md()).to_vec())
                .collect(),
        )
    }
}

impl Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_md(&self.to_md()))
    }
}

impl Display for Arguments {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render_md(&self.to_md()))
    }
}

fn parse_goal(nodes: &[Node]) -> Goal {
    let mut index = 0;
    let givens = if paragraph_is_label(nodes.get(index), "Given:") {
        index += 1;
        let Node::List(List {
            children,
            ordered: false,
            ..
        }) = nodes
            .get(index)
            .unwrap_or_else(|| panic!("Given must be followed by an unordered expression list"))
        else {
            panic!("Given must be followed by an unordered expression list")
        };
        assert!(!children.is_empty(), "Given list must not be empty");
        index += 1;
        children.iter().map(parse_expression_item).collect()
    } else {
        Vec::new()
    };
    let (conclusion, tactic) = parse_wts(
        nodes
            .get(index)
            .unwrap_or_else(|| panic!("goal must contain WTS")),
    );
    index += 1;
    let steps = if let Some(node) = nodes.get(index) {
        index += 1;
        parse_argument_items(node)
    } else {
        Vec::new()
    };
    assert_eq!(index, nodes.len(), "unexpected content after goal");
    Goal {
        givens,
        conclusion,
        tactic,
        steps,
        validation: StepValidationData::default(),
    }
}

fn paragraph_is_label(node: Option<&Node>, expected: &str) -> bool {
    matches!(
        node,
        Some(Node::Paragraph(Paragraph { children, .. }))
            if matches!(children.as_slice(), [Node::Text(text)] if text.value == expected)
    )
}

fn parse_wts(node: &Node) -> (Expr<()>, Option<Tactic>) {
    let Node::Paragraph(Paragraph { children, .. }) = node else {
        panic!("WTS must be a paragraph")
    };
    let (label, math, tactic) = match children.as_slice() {
        [Node::Text(label), Node::InlineMath(math)] => (label, math, None),
        [
            Node::Text(label),
            Node::InlineMath(math),
            Node::Text(tactic_label),
            Node::InlineMath(variable),
        ] => {
            assert_eq!(
                tactic_label.value, " by induction on ",
                "unsupported goal tactic"
            );
            let parsed =
                ratex_parser::parse(&variable.value).expect("invalid TeX in induction variable");
            let variable =
                crate::from_tex::expr(&parsed).expect("unsupported TeX in induction variable");
            let RawExpr::Variable(variable) = &variable.raw else {
                panic!("induction target must be a variable")
            };
            (
                label,
                math,
                Some(Tactic::Induction {
                    variable: variable.clone(),
                }),
            )
        }
        _ => panic!("WTS must contain one expression and an optional supported tactic"),
    };
    assert_eq!(label.value, "WTS ", "goal paragraph must start with WTS");
    let parsed = ratex_parser::parse(&math.value).expect("invalid TeX in WTS expression");
    (
        crate::from_tex::expr(&parsed).expect("unsupported TeX in WTS expression"),
        tactic,
    )
}

fn parse_argument_items(node: &Node) -> Vec<ArgumentItem> {
    let Node::List(List {
        children,
        ordered: true,
        ..
    }) = node
    else {
        panic!("goal body must be an ordered list")
    };
    children.iter().map(parse_argument_item).collect()
}

fn parse_argument_item(node: &Node) -> ArgumentItem {
    let Node::ListItem(ListItem { children, .. }) = node else {
        panic!("argument item must be a list item")
    };
    if matches!(children.first(), Some(Node::Paragraph(Paragraph { children, .. })) if matches!(children.first(), Some(Node::InlineMath(_))))
    {
        return ArgumentItem::Sentence(ArgumentStep {
            sentence: parse_expression_item(node),
            validation: StepValidationData::default(),
        });
    }
    ArgumentItem::Goal(parse_goal(children))
}

fn goal_nodes(goal: &Goal, expressions: &[Expr<()>]) -> Vec<Node> {
    let mut nodes = Vec::new();
    if !goal.givens.is_empty() {
        nodes.push(text_paragraph("Given:"));
        nodes.push(expression_list(&goal.givens));
    }
    let mut wts_children = vec![
        Node::Text(::markdown::mdast::Text {
            value: "WTS ".to_owned(),
            position: None,
        }),
        Node::InlineMath(InlineMath {
            value: goal.conclusion.as_latex().to_string(),
            position: None,
        }),
    ];
    if let Some(Tactic::Induction { variable }) = &goal.tactic {
        wts_children.push(Node::Text(::markdown::mdast::Text {
            value: " by induction on ".to_owned(),
            position: None,
        }));
        let variable_expression: Expr<()> = Expr::new(RawExpr::Variable(variable.clone()));
        wts_children.push(Node::InlineMath(InlineMath {
            value: variable_expression.as_latex().to_string(),
            position: None,
        }));
    }
    nodes.push(Node::Paragraph(Paragraph {
        children: wts_children,
        position: None,
    }));
    if let Some(details) = validation_details(&goal.conclusion, &goal.validation, expressions) {
        nodes.push(Node::Html(Html {
            value: details,
            position: None,
        }));
    }
    if !goal.steps.is_empty() {
        nodes.push(argument_item_list(&goal.steps, expressions));
    }
    nodes
}

fn text_paragraph(value: &str) -> Node {
    Node::Paragraph(Paragraph {
        children: vec![Node::Text(::markdown::mdast::Text {
            value: value.to_owned(),
            position: None,
        })],
        position: None,
    })
}

fn argument_item_list(items: &[ArgumentItem], expressions: &[Expr<()>]) -> Node {
    Node::List(List {
        children: items
            .iter()
            .map(|item| {
                let children = match item {
                    ArgumentItem::Sentence(step) => {
                        let mut children = vec![Node::Paragraph(Paragraph {
                            children: vec![Node::InlineMath(InlineMath {
                                value: step.sentence.as_latex().to_string(),
                                position: None,
                            })],
                            position: None,
                        })];
                        if let Some(details) =
                            validation_details(&step.sentence, &step.validation, expressions)
                        {
                            children.push(Node::Html(Html {
                                value: details,
                                position: None,
                            }));
                        }
                        children
                    }
                    ArgumentItem::Goal(goal) => goal_nodes(goal, expressions),
                };
                Node::ListItem(ListItem {
                    children,
                    position: None,
                    spread: true,
                    checked: None,
                })
            })
            .collect(),
        position: None,
        ordered: true,
        start: Some(1),
        spread: true,
    })
}

fn validation_details(
    sentence: &Expr<()>,
    validation: &StepValidationData,
    expressions: &[Expr<()>],
) -> Option<String> {
    if let Some(StepCheck::Counterexample { model, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Counterexample { .. }))
    {
        let assignments = expression_bullets(model);
        return Some(format!(
            "<details>\n<summary>❌ counterexample found</summary>\n\nThe negation of ${}$ is satisfied by:\n\n{assignments}\n</details>",
            sentence.as_latex()
        ));
    }
    if let Some(StepCheck::DimensionallyInvalid { declarations, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::DimensionallyInvalid { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ dimensionally invalid</summary>\n\nThis step is not dimensionally meaningful in the following environment:\n\n{}\n</details>",
            expression_bullets(declarations)
        ));
    }
    if let Some(StepCheck::Error { error, .. }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::Error { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Unsupported step</summary>\n\n{error}\n</details>"
        ));
    }
    if let Some(StepCheck::InvalidTactic { message }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InvalidTactic { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ invalid tactic</summary>\n\n{message}\n</details>"
        ));
    }
    if let Some(StepCheck::InvalidExistentialElimination { message }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InvalidExistentialElimination { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Invalid existential elimination</summary>\n\n{message}\n</details>"
        ));
    }
    let existence_warnings: Vec<_> = validation
        .checks
        .iter()
        .filter(|check| {
            matches!(
                check,
                StepCheck::MayBeUndefined { .. } | StepCheck::AssumedExistence { .. }
            )
        })
        .collect();
    if !existence_warnings.is_empty() {
        let mut messages = Vec::new();
        for warning in existence_warnings {
            match warning {
                StepCheck::MayBeUndefined {
                    introduced_variable,
                    witness,
                    ..
                } => messages.push(format!(
                    "The expression ${}$ may be undefined. For example:\n\n{}",
                    introduced_variable.name,
                    expression_bullets(witness)
                )),
                StepCheck::AssumedExistence {
                    introduced_variable,
                    ..
                } => messages.push(format!(
                    "The existence of ${}$ was assumed without checking.",
                    introduced_variable.name
                )),
                _ => unreachable!(),
            }
        }
        return Some(format!(
            "<details>\n<summary>⚠️ conditional</summary>\n\n{}\n</details>",
            messages.join("\n\n")
        ));
    }
    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::Unknown { .. }))
    {
        return Some(
            "<details>\n<summary>Inconclusive</summary>\n\nZ3 could not determine whether a counterexample exists in every environment tried.\n</details>"
                .to_owned(),
        );
    }
    if let Some(StepCheck::QuantifierInconclusive { message }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::QuantifierInconclusive { .. }))
    {
        return Some(format!(
            "<details>\n<summary>Inconclusive</summary>\n\n{message}\n</details>"
        ));
    }
    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::VacuousQuantifier))
    {
        return Some(
            "<details>\n<summary>Inconclusive</summary>\n\nThe quantified premises had no admissible instance in the environments checked.\n</details>"
                .to_owned(),
        );
    }
    if let Some(StepCheck::ExistentialWitness {
        assignments,
        supporting_facts,
    }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::ExistentialWitness { .. }))
    {
        let assignments = assignments
            .iter()
            .map(|(variable, expression)| {
                format!("- ${} = {}$", variable.z3_name(), expression.as_latex())
            })
            .collect::<Vec<_>>()
            .join("\n");
        let warning = validation
            .checks
            .iter()
            .find_map(|check| match check {
                StepCheck::QuestionableQuantifier { premises } => Some(format!(
                    "\n\nThe following premises do not reference a variable introduced by their quantifier:\n\n{}",
                    expression_bullets(premises)
                )),
                _ => None,
            })
            .unwrap_or_default();
        return Some(format!(
            "<details>\n<summary>✅ witness found</summary>\n\nWitness:\n\n{assignments}\n\nMatched facts:\n\n{}{warning}\n</details>",
            expression_bullets(supporting_facts)
        ));
    }
    if let Some(StepCheck::ExistentialElimination { fact, assignments }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::ExistentialElimination { .. }))
    {
        let assignments = assignments
            .iter()
            .map(|(binder, witness)| {
                format!(
                    "- ${}$ as a witness for ${}$",
                    witness.z3_name(),
                    binder.z3_name()
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        return Some(format!(
            "<details>\n<summary>✅ witness introduced</summary>\n\nFrom ${}$:\n\n{assignments}\n</details>",
            fact.as_latex()
        ));
    }
    if let Some(StepCheck::QuestionableQuantifier { premises }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::QuestionableQuantifier { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ questionable quantifier</summary>\n\nThe following premises do not reference a variable introduced by their quantifier:\n\n{}\n</details>",
            expression_bullets(premises)
        ));
    }
    if let Some(StepCheck::IncompleteSubgoals { expected }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::IncompleteSubgoals { .. }))
    {
        return Some(format!(
            "<details>\n<summary>⚠️ valid claim, incomplete subgoals</summary>\n\nNo counterexample was found, but the following subgoals were not established:\n\n{}\n</details>",
            expression_bullets(expected)
        ));
    }
    if let Some(StepCheck::InconsistentGivens { max_dimension }) = validation
        .checks
        .iter()
        .find(|check| matches!(check, StepCheck::InconsistentGivens { .. }))
    {
        let message = match max_dimension {
            Some(max_dimension) => {
                format!("The givens are inconsistent up to dimension {max_dimension}.")
            }
            None => "The givens are inconsistent.".to_owned(),
        };
        return Some(format!(
            "<details>\n<summary>Inconsistent givens</summary>\n\n{message}\n</details>"
        ));
    }
    if validation.checks.is_empty() {
        return None;
    }

    if validation
        .checks
        .iter()
        .any(|check| matches!(check, StepCheck::TacticEstablished))
    {
        if validation.environments_exhaustive {
            return Some(
                "<details>\n<summary>✅ verified</summary>\n\nThe induction base and step were validated.\n</details>"
                    .to_owned(),
            );
        }
        let max_dimension = validation
            .max_dimension
            .unwrap_or_else(|| panic!("validated goal is missing its maximum dimension"));
        return Some(format!(
            "<details>\n<summary>✅ likely</summary>\n\nThe induction base and step were validated up to a maximum dimension of {max_dimension}.\n</details>"
        ));
    }

    let mut present = BTreeSet::new();
    for check in &validation.checks {
        match check {
            StepCheck::Unsat {
                supporting_facts, ..
            } => present.extend(supporting_facts.iter().cloned()),
            StepCheck::EstablishedByFact { fact } => {
                present.insert(fact.clone());
            }
            _ => {}
        }
    }
    let mut seen = BTreeSet::new();
    let supporting_facts: Vec<_> = expressions
        .iter()
        .filter(|expression| present.contains(*expression) && seen.insert((*expression).clone()))
        .cloned()
        .collect();
    let explanation = if supporting_facts.is_empty() {
        "No premises seemed necessary to show this.".to_owned()
    } else if validation.environments_exhaustive {
        format!(
            "This follows from the following facts:\n\n{}",
            expression_bullets(&supporting_facts)
        )
    } else {
        format!(
            "This may follow from the following facts:\n\n{}",
            expression_bullets(&supporting_facts)
        )
    };
    if validation.environments_exhaustive {
        Some(format!(
            "<details>\n<summary>✅ verified</summary>\n\n{explanation}\n</details>"
        ))
    } else {
        let max_dimension = validation
            .max_dimension
            .unwrap_or_else(|| panic!("validated step is missing its maximum dimension"));
        Some(format!(
            "<details>\n<summary>✅ likely</summary>\n\nNo counterexamples found up to a maximum dimension of {max_dimension}.\n\n{explanation}\n</details>"
        ))
    }
}

fn argument_expressions(argument: &Argument) -> Vec<Expr<()>> {
    fn collect(goal: &Goal, expressions: &mut Vec<Expr<()>>) {
        expressions.extend(goal.givens.iter().cloned());
        for item in &goal.steps {
            match item {
                ArgumentItem::Sentence(step) => expressions.push(step.sentence.clone()),
                ArgumentItem::Goal(goal) => collect(goal, expressions),
            }
        }
        expressions.push(goal.conclusion.clone());
    }

    let mut expressions = Vec::new();
    collect(&argument.root, &mut expressions);
    expressions
}

fn expression_bullets(expressions: &[Expr<()>]) -> String {
    expressions
        .iter()
        .map(|expression| format!("- ${}$", expression.as_latex()))
        .collect::<Vec<_>>()
        .join("\n")
}
