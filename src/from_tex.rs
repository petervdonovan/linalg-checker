use std::{error::Error, fmt};

use ratex_parser::{ParseNode, parse_node::AtomFamily};

use crate::{
    Annotation, Binop, Cmp, CmpChain, Expr, Finop, Logic, LogicChain, Matrix, Monop, RawExpr,
    SeqOp, SeqopRange, Triop, Type, Variable,
};

#[derive(Debug, PartialEq, Eq)]
pub enum FromTexError {
    EmptyExpression,
    UnexpectedEnd { context: &'static str },
    UnexpectedNode { index: usize, kind: &'static str },
    Unsupported { index: usize, syntax: String },
    Malformed { index: usize, message: String },
    TrailingNodes { index: usize },
}

impl fmt::Display for FromTexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyExpression => write!(f, "empty expression"),
            Self::UnexpectedEnd { context } => {
                write!(f, "unexpected end while parsing {context}")
            }
            Self::UnexpectedNode { index, kind } => {
                write!(f, "unexpected {kind} node at index {index}")
            }
            Self::Unsupported { index, syntax } => {
                write!(f, "unsupported syntax at index {index}: {syntax}")
            }
            Self::Malformed { index, message } => {
                write!(f, "malformed expression at index {index}: {message}")
            }
            Self::TrailingNodes { index } => {
                write!(f, "unconsumed parse nodes starting at index {index}")
            }
        }
    }
}

impl Error for FromTexError {}

pub fn expr(nodes: &[ParseNode]) -> Result<Expr<()>, FromTexError> {
    Cursor::new(nodes).parse_complete()
}

struct Cursor<'a> {
    nodes: &'a [ParseNode],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(nodes: &'a [ParseNode]) -> Self {
        Self { nodes, position: 0 }
    }

    fn parse_complete(mut self) -> Result<Expr<()>, FromTexError> {
        if self.nodes.is_empty() {
            return Err(FromTexError::EmptyExpression);
        }
        self.skip_ignorable();
        let expression = self.parse_logic()?;
        self.skip_ignorable();
        if self.position != self.nodes.len() {
            return Err(FromTexError::TrailingNodes {
                index: self.position,
            });
        }
        Ok(expression)
    }

    fn parse_logic(&mut self) -> Result<Expr<()>, FromTexError> {
        let start = self.parse_comparison()?;
        let mut assertions = Vec::new();

        loop {
            self.skip_ignorable();
            let Some(op) = self.current_logic_operator() else {
                break;
            };
            self.position += 1;
            self.skip_ignorable();
            assertions.push((op, self.parse_comparison()?));
        }

        if assertions.is_empty() {
            Ok(start)
        } else {
            Ok(Expr::new(RawExpr::LogicChain(LogicChain {
                start,
                assertions,
            })))
        }
    }

    fn parse_comparison(&mut self) -> Result<Expr<()>, FromTexError> {
        let start = self.parse_addition()?;
        self.skip_ignorable();
        if self.current_atom_text() == Some(r"\in") {
            self.position += 1;
            self.skip_ignorable();
            let right = self.parse_addition()?;
            self.skip_ignorable();
            if self.current_comparison_operator().is_some()
                || self.current_atom_text() == Some(r"\in")
            {
                return Err(FromTexError::Malformed {
                    index: self.position,
                    message: "membership cannot be chained".to_owned(),
                });
            }
            return Ok(Expr::new(RawExpr::Binop(Binop::ElementOf, start, right)));
        }
        let mut assertions = Vec::new();

        while let Some(op) = self.current_comparison_operator() {
            self.position += 1;
            assertions.push((op, self.parse_addition()?));
        }

        if assertions.is_empty() {
            Ok(start)
        } else {
            Ok(Expr::new(RawExpr::CmpChain(CmpChain { start, assertions })))
        }
    }

    fn parse_addition(&mut self) -> Result<Expr<()>, FromTexError> {
        let first = self.parse_multiplication()?;
        let mut terms = Vec::new();
        push_associative(&mut terms, first, FinopKind::Plus);

        while let Some(operator) = self.current_atom_text() {
            let is_subtraction = operator == "-";
            if operator != "+" && !is_subtraction {
                break;
            }
            self.position += 1;
            let mut term = self.parse_multiplication()?;
            if is_subtraction {
                term = Expr::new(RawExpr::Monop(Monop::Neg, term));
            }
            push_associative(&mut terms, term, FinopKind::Plus);
        }

        if terms.len() == 1 {
            Ok(terms.pop().unwrap())
        } else {
            Ok(Expr::new(RawExpr::Finop(Finop::Plus, terms)))
        }
    }

    fn parse_multiplication(&mut self) -> Result<Expr<()>, FromTexError> {
        let first = self.parse_prefix()?;
        let mut factors = Vec::new();
        push_associative(&mut factors, first, FinopKind::Times);

        while self.starts_primary() {
            let factor = self.parse_prefix()?;
            push_associative(&mut factors, factor, FinopKind::Times);
        }

        if factors.len() == 1 {
            Ok(factors.pop().unwrap())
        } else {
            Ok(Expr::new(RawExpr::Finop(Finop::Times, factors)))
        }
    }

    fn parse_prefix(&mut self) -> Result<Expr<()>, FromTexError> {
        if self.current_atom_text() == Some("-") {
            self.position += 1;
            return Ok(Expr::new(RawExpr::Monop(Monop::Neg, self.parse_prefix()?)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Expr<()>, FromTexError> {
        let current = self
            .nodes
            .get(self.position)
            .ok_or(FromTexError::UnexpectedEnd {
                context: "an operand",
            })?;

        if let Some((op, range)) = parse_sequence_head(current)? {
            self.position += 1;
            let body = self.parse_multiplication()?;
            return Ok(Expr::new(RawExpr::Seqop(op, range, body)));
        }
        if let Some(ty) = parse_type(current)? {
            self.position += 1;
            return Ok(Expr::new(RawExpr::Type(ty)));
        }

        match current {
            ParseNode::TextOrd { text, .. } if text == r"\square" => {
                self.position += 1;
                Ok(Expr::new(RawExpr::Hole))
            }
            ParseNode::TextOrd { text, .. }
                if text.chars().all(|character| character.is_ascii_digit()) =>
            {
                self.parse_natural()
            }
            ParseNode::MathOrd { .. } => self.parse_variable_name(),
            ParseNode::OrdGroup { body, .. } => {
                self.position += 1;
                expr(body)
            }
            ParseNode::LeftRight {
                body, left, right, ..
            } if left == "[" && right == "]" => {
                self.position += 1;
                parse_bmatrix(body)
            }
            ParseNode::LeftRight {
                body, left, right, ..
            } if left == "(" && right == ")" => {
                self.position += 1;
                expr(body)
            }
            ParseNode::GenFrac {
                numer,
                denom,
                has_bar_line: true,
                ..
            } => {
                self.position += 1;
                Ok(Expr::new(RawExpr::Binop(
                    Binop::Div,
                    parse_group(numer)?,
                    parse_group(denom)?,
                )))
            }
            ParseNode::Accent { .. } | ParseNode::SupSub { .. } => {
                self.position += 1;
                parse_decorated(current)
            }
            ParseNode::OperatorName { body, .. } => {
                let name = collect_text(body).ok_or_else(|| FromTexError::Malformed {
                    index: self.position,
                    message: "operator name is not plain text".to_owned(),
                })?;
                let op = match name.as_str() {
                    "tr" => Monop::Trace,
                    "det" => Monop::Det,
                    _ => return Err(self.unsupported(format!("operator name {name}"))),
                };
                self.position += 1;
                let argument = self.take_parenthesized()?;
                Ok(Expr::new(RawExpr::Monop(op, expr(argument)?)))
            }
            ParseNode::Op {
                name: Some(name), ..
            } if name == r"\max" || name == r"\min" => {
                let op = if name == r"\max" {
                    Finop::Max
                } else {
                    Finop::Min
                };
                self.position += 1;
                let arguments = self.take_parenthesized()?;
                let parts = split_top_level(arguments, ",");
                if parts.is_empty() || parts.iter().any(|part| part.is_empty()) {
                    return Err(FromTexError::Malformed {
                        index: self.position,
                        message: "empty max/min argument".to_owned(),
                    });
                }
                let expressions = parts.into_iter().map(expr).collect::<Result<Vec<_>, _>>()?;
                Ok(Expr::new(RawExpr::Finop(op, expressions)))
            }
            ParseNode::Atom {
                family: AtomFamily::Open,
                text,
                ..
            } if text == "(" => {
                let body = self.take_parenthesized()?;
                expr(body)
            }
            ParseNode::Atom {
                family: AtomFamily::Open,
                text,
                ..
            } if text == r"\langle" => self.parse_inner_product(),
            other => Err(FromTexError::Unsupported {
                index: self.position,
                syntax: other.type_name().to_owned(),
            }),
        }
    }

    fn parse_natural(&mut self) -> Result<Expr<()>, FromTexError> {
        let start = self.position;
        let mut digits = String::new();
        while let Some(ParseNode::TextOrd { text, .. }) = self.nodes.get(self.position) {
            if !text.chars().all(|character| character.is_ascii_digit()) {
                break;
            }
            digits.push_str(text);
            self.position += 1;
        }
        let value = digits.parse().map_err(|_| FromTexError::Malformed {
            index: start,
            message: "natural-number literal does not fit in u64".to_owned(),
        })?;
        Ok(Expr::new(RawExpr::NatLiteral(value)))
    }

    fn parse_variable_name(&mut self) -> Result<Expr<()>, FromTexError> {
        let ParseNode::MathOrd { text: name, .. } = &self.nodes[self.position] else {
            unreachable!("parse_variable_name is only called for MathOrd nodes")
        };
        self.position += 1;
        Ok(Expr::new(RawExpr::Variable(Variable {
            name: name.clone(),
            non_numeric_subscript: String::new(),
            annotations: Vec::new(),
        })))
    }

    fn parse_inner_product(&mut self) -> Result<Expr<()>, FromTexError> {
        let start = self.position;
        self.position += 1;
        let body_start = self.position;
        while self.position < self.nodes.len() {
            if matches!(
                self.nodes.get(self.position),
                Some(ParseNode::Atom {
                    family: AtomFamily::Close,
                    text,
                    ..
                }) if text == r"\rangle"
            ) {
                let body = &self.nodes[body_start..self.position];
                self.position += 1;
                let parts = split_top_level(body, ",");
                if parts.len() != 2 {
                    return Err(FromTexError::Malformed {
                        index: start,
                        message: "inner product requires two arguments".to_owned(),
                    });
                }
                return Ok(Expr::new(RawExpr::Binop(
                    Binop::InnerProd,
                    expr(parts[0])?,
                    expr(parts[1])?,
                )));
            }
            self.position += 1;
        }
        Err(FromTexError::UnexpectedEnd {
            context: "an inner product",
        })
    }

    fn take_parenthesized(&mut self) -> Result<&'a [ParseNode], FromTexError> {
        if !is_atom(self.nodes.get(self.position), AtomFamily::Open, "(") {
            return Err(FromTexError::Malformed {
                index: self.position,
                message: "expected an opening parenthesis".to_owned(),
            });
        }
        let start = self.position + 1;
        let mut depth = 1usize;
        let mut cursor = start;
        while cursor < self.nodes.len() {
            if is_atom(self.nodes.get(cursor), AtomFamily::Open, "(") {
                depth += 1;
            } else if is_atom(self.nodes.get(cursor), AtomFamily::Close, ")") {
                depth -= 1;
                if depth == 0 {
                    self.position = cursor + 1;
                    return Ok(&self.nodes[start..cursor]);
                }
            }
            cursor += 1;
        }
        Err(FromTexError::UnexpectedEnd {
            context: "a parenthesized expression",
        })
    }

    fn current_atom_text(&self) -> Option<&str> {
        match self.nodes.get(self.position) {
            Some(ParseNode::Atom { text, .. }) => Some(text),
            _ => None,
        }
    }

    fn current_comparison_operator(&self) -> Option<Cmp> {
        match self.current_atom_text()? {
            "=" => Some(Cmp::Eq),
            "<" => Some(Cmp::Lt),
            ">" => Some(Cmp::Gt),
            r"\le" | r"\leq" => Some(Cmp::Le),
            r"\ge" | r"\geq" => Some(Cmp::Ge),
            _ => None,
        }
    }

    fn current_logic_operator(&self) -> Option<Logic> {
        match self.current_atom_text()? {
            r"\Longrightarrow" | r"\implies" => Some(Logic::Imp),
            r"\Longleftrightarrow" | r"\iff" => Some(Logic::Iff),
            _ => None,
        }
    }

    fn skip_ignorable(&mut self) {
        while matches!(
            self.nodes.get(self.position),
            Some(ParseNode::Kern { .. } | ParseNode::SpacingNode { .. })
        ) {
            self.position += 1;
        }
    }

    fn starts_primary(&self) -> bool {
        match self.nodes.get(self.position) {
            Some(ParseNode::MathOrd { .. }) => true,
            Some(ParseNode::TextOrd { text, .. }) => {
                text == r"\square" || text.chars().all(|character| character.is_ascii_digit())
            }
            Some(
                ParseNode::OrdGroup { .. }
                | ParseNode::LeftRight { .. }
                | ParseNode::GenFrac { .. }
                | ParseNode::Accent { .. }
                | ParseNode::SupSub { .. }
                | ParseNode::Font { .. }
                | ParseNode::OperatorName { .. }
                | ParseNode::Op { .. },
            ) => true,
            Some(ParseNode::Atom {
                family: AtomFamily::Open,
                text,
                ..
            }) => text == "(" || text == r"\langle",
            _ => false,
        }
    }

    fn unsupported(&self, syntax: String) -> FromTexError {
        FromTexError::Unsupported {
            index: self.position,
            syntax,
        }
    }
}

fn parse_type(node: &ParseNode) -> Result<Option<Type>, FromTexError> {
    match node {
        ParseNode::Font { font, .. } if font == "mathbb" => {
            Ok(type_base(node).map(|ty| match ty {
                Type::Matrix(_, _) => unreachable!(),
                ty => ty,
            }))
        }
        ParseNode::SupSub {
            base: Some(base),
            sup: Some(sup),
            sub: None,
            ..
        } if type_base(base) == Some(Type::Real) => {
            let dimensions = group_body(sup);
            let parts = split_top_level(dimensions, r"\times");
            let dimension = |nodes: &[ParseNode]| -> Result<u64, FromTexError> {
                let text = collect_text(
                    &nodes
                        .iter()
                        .filter(|node| {
                            !matches!(node, ParseNode::Kern { .. } | ParseNode::SpacingNode { .. })
                        })
                        .cloned()
                        .collect::<Vec<_>>(),
                )
                .ok_or_else(|| FromTexError::Malformed {
                    index: 0,
                    message: "type dimension must be a natural-number literal".to_owned(),
                })?;
                text.parse().map_err(|_| FromTexError::Malformed {
                    index: 0,
                    message: "type dimension does not fit in u64".to_owned(),
                })
            };
            match parts.as_slice() {
                [size] => Ok(Some(Type::Matrix(dimension(size)?, 1))),
                [rows, cols] => Ok(Some(Type::Matrix(dimension(rows)?, dimension(cols)?))),
                _ => Err(FromTexError::Malformed {
                    index: 0,
                    message: "matrix type requires one or two dimensions".to_owned(),
                }),
            }
        }
        _ => Ok(None),
    }
}

fn type_base(node: &ParseNode) -> Option<Type> {
    let ParseNode::Font { font, body, .. } = node else {
        return None;
    };
    if font != "mathbb" {
        return None;
    }
    match collect_text(group_body(body)).as_deref()? {
        "B" => Some(Type::Bool),
        "N" => Some(Type::Nat),
        "Z" => Some(Type::Int),
        "R" => Some(Type::Real),
        _ => None,
    }
}

fn parse_group(group: &ParseNode) -> Result<Expr<()>, FromTexError> {
    match group {
        ParseNode::OrdGroup { body, .. } => expr(body),
        node => expr(std::slice::from_ref(node)),
    }
}

fn parse_bmatrix(body: &[ParseNode]) -> Result<Expr<()>, FromTexError> {
    let [ParseNode::Array { body: rows, .. }] = body else {
        return Err(FromTexError::Unsupported {
            index: 0,
            syntax: "bracketed expression is not a bmatrix".to_owned(),
        });
    };

    let columns = rows.first().map_or(0, Vec::len);
    if rows.iter().any(|row| row.len() != columns) {
        return Err(FromTexError::Malformed {
            index: 0,
            message: "matrix rows have different lengths".to_owned(),
        });
    }

    let elements = rows
        .iter()
        .flatten()
        .map(parse_matrix_cell)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Expr::new(RawExpr::Matrix(Matrix {
        rows: rows.len(),
        cols: columns,
        elements,
    })))
}

fn parse_matrix_cell(cell: &ParseNode) -> Result<Expr<()>, FromTexError> {
    match cell {
        ParseNode::Styling { body, .. } => expr(body),
        other => Err(FromTexError::Malformed {
            index: 0,
            message: format!("matrix cell is unexpectedly a {}", other.type_name()),
        }),
    }
}

fn parse_decorated(node: &ParseNode) -> Result<Expr<()>, FromTexError> {
    match node {
        ParseNode::Accent { label, base, .. } => {
            let annotation = match label.as_str() {
                r"\hat" => Annotation::Hat,
                r"\tilde" => Annotation::Tilde,
                r"\vec" => Annotation::Arrow,
                _ => {
                    return Err(FromTexError::Unsupported {
                        index: 0,
                        syntax: format!("accent {label}"),
                    });
                }
            };
            let mut expression = parse_group(base)?;
            let variable = variable_mut(&mut expression, "accent")?;
            variable.annotations.push(annotation);
            Ok(expression)
        }
        ParseNode::SupSub {
            base: Some(base),
            sup,
            sub,
            ..
        } => parse_sup_sub(base, sup.as_deref(), sub.as_deref()),
        ParseNode::SupSub { .. } => Err(FromTexError::Malformed {
            index: 0,
            message: "script has no base".to_owned(),
        }),
        other => Err(FromTexError::UnexpectedNode {
            index: 0,
            kind: other.type_name(),
        }),
    }
}

fn parse_sup_sub(
    base: &ParseNode,
    sup: Option<&ParseNode>,
    sub: Option<&ParseNode>,
) -> Result<Expr<()>, FromTexError> {
    if let ParseNode::LeftRight {
        body, left, right, ..
    } = base
        && left == r"\lVert"
        && right == r"\rVert"
        && sup.is_none()
    {
        let op = norm_operator(sub.ok_or_else(|| FromTexError::Malformed {
            index: 0,
            message: "norm is missing its subscript".to_owned(),
        })?)?;
        return Ok(Expr::new(RawExpr::Monop(op, expr(body)?)));
    }

    let mut expression = parse_group(base)?;

    if let Some(subscript) = sub {
        let body = group_body(subscript);
        let parts = split_top_level(body, ",");
        if parts.len() == 2 {
            expression = Expr::new(RawExpr::Triop(
                Triop::DoubleSubscript,
                expression,
                expr(parts[0])?,
                expr(parts[1])?,
            ));
        } else if let Some(name) = collect_text(body).filter(|name| {
            !name.is_empty() && !name.chars().all(|character| character.is_ascii_digit())
        }) {
            if let Ok(variable) = variable_mut(&mut expression, "subscript") {
                variable.non_numeric_subscript = name;
            } else {
                expression = Expr::new(RawExpr::Binop(
                    Binop::SingleSubscript,
                    expression,
                    expr(body)?,
                ));
            }
        } else {
            expression = Expr::new(RawExpr::Binop(
                Binop::SingleSubscript,
                expression,
                expr(body)?,
            ));
        }
    }

    if let Some(superscript) = sup {
        let body = group_body(superscript);
        if is_prime(body) {
            variable_mut(&mut expression, "prime")?
                .annotations
                .push(Annotation::Prime);
        } else if is_minus_one(body) {
            expression = Expr::new(RawExpr::Monop(Monop::Inverse, expression));
        } else {
            expression = Expr::new(RawExpr::Binop(Binop::Power, expression, expr(body)?));
        }
    }

    Ok(expression)
}

fn parse_sequence_head(node: &ParseNode) -> Result<Option<(SeqOp, SeqopRange<()>)>, FromTexError> {
    let ParseNode::SupSub {
        base: Some(base),
        sup: Some(sup),
        sub: Some(sub),
        ..
    } = node
    else {
        return Ok(None);
    };
    let ParseNode::Op {
        name: Some(name), ..
    } = base.as_ref()
    else {
        return Ok(None);
    };
    let op = match name.as_str() {
        r"\sum" => SeqOp::Sum,
        r"\prod" => SeqOp::Prod,
        _ => return Ok(None),
    };
    let lower = group_body(sub);
    let parts = split_top_level(lower, "=");
    if parts.len() != 2 {
        return Err(FromTexError::Malformed {
            index: 0,
            message: "sequence lower limit must have the form i=from".to_owned(),
        });
    }
    let index_expression = expr(parts[0])?;
    let index_variable = match &index_expression.raw {
        RawExpr::Variable(variable) => Variable {
            name: variable.name.clone(),
            non_numeric_subscript: variable.non_numeric_subscript.clone(),
            annotations: Vec::new(),
        },
        _ => {
            return Err(FromTexError::Malformed {
                index: 0,
                message: "sequence index must be a variable".to_owned(),
            });
        }
    };
    Ok(Some((
        op,
        SeqopRange {
            index_variable,
            from: expr(parts[1])?,
            to: parse_group(sup)?,
        },
    )))
}

fn norm_operator(subscript: &ParseNode) -> Result<Monop, FromTexError> {
    let text = collect_text(group_body(subscript)).ok_or_else(|| FromTexError::Malformed {
        index: 0,
        message: "norm subscript is not plain text".to_owned(),
    })?;
    match text.as_str() {
        "1" => Ok(Monop::Norm1),
        "2" => Ok(Monop::Norm2),
        r"\infty" => Ok(Monop::NormInfty),
        "F" => Ok(Monop::NormFrob),
        _ => Err(FromTexError::Unsupported {
            index: 0,
            syntax: format!("norm subscript {text}"),
        }),
    }
}

fn group_body(node: &ParseNode) -> &[ParseNode] {
    match node {
        ParseNode::OrdGroup { body, .. } => body,
        node => std::slice::from_ref(node),
    }
}

fn collect_text(nodes: &[ParseNode]) -> Option<String> {
    let mut result = String::new();
    for node in nodes {
        match node {
            ParseNode::MathOrd { text, .. } | ParseNode::TextOrd { text, .. } => {
                result.push_str(text)
            }
            _ => return None,
        }
    }
    Some(result)
}

fn is_prime(nodes: &[ParseNode]) -> bool {
    collect_text(nodes).as_deref() == Some(r"\prime")
}

fn is_minus_one(nodes: &[ParseNode]) -> bool {
    nodes.len() == 2
        && is_atom(nodes.first(), AtomFamily::Bin, "-")
        && matches!(nodes.get(1), Some(ParseNode::TextOrd { text, .. }) if text == "1")
}

fn split_top_level<'a>(nodes: &'a [ParseNode], delimiter: &str) -> Vec<&'a [ParseNode]> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut depth = 0usize;
    for (index, node) in nodes.iter().enumerate() {
        if is_atom(Some(node), AtomFamily::Open, "(") {
            depth += 1;
        } else if is_atom(Some(node), AtomFamily::Close, ")") {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && matches!(node, ParseNode::Atom { text, .. } if text == delimiter) {
            parts.push(&nodes[start..index]);
            start = index + 1;
        }
    }
    parts.push(&nodes[start..]);
    parts
}

fn is_atom(node: Option<&ParseNode>, family: AtomFamily, text: &str) -> bool {
    matches!(
        node,
        Some(ParseNode::Atom {
            family: actual_family,
            text: actual_text,
            ..
        }) if *actual_family == family && actual_text == text
    )
}

fn variable_mut<'a>(
    expression: &'a mut Expr<()>,
    context: &'static str,
) -> Result<&'a mut Variable, FromTexError> {
    match &mut expression
        .get_mut()
        .expect("newly parsed expressions are not shared")
        .raw
    {
        RawExpr::Variable(variable) => Ok(variable),
        _ => Err(FromTexError::Malformed {
            index: 0,
            message: format!("{context} is only supported on variables"),
        }),
    }
}

enum FinopKind {
    Plus,
    Times,
}

fn push_associative(expressions: &mut Vec<Expr<()>>, expression: Expr<()>, kind: FinopKind) {
    match (&expression.raw, kind) {
        (RawExpr::Finop(Finop::Plus, nested), FinopKind::Plus)
        | (RawExpr::Finop(Finop::Times, nested), FinopKind::Times) => {
            expressions.extend(nested.iter().cloned())
        }
        _ => expressions.push(expression),
    }
}

#[cfg(test)]
mod tests {
    use std::fmt;

    use expect_test::expect;
    use ratex_parser::parse;

    use super::FromTexError;
    use crate::{Binop, Expr, RawExpr, Type};

    struct Latex(Expr<()>);

    impl fmt::Display for Latex {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            crate::to_tex::expr(f, &self.0)
        }
    }

    fn round_trip(input: &str) -> Result<String, FromTexError> {
        let parsed = parse(input).expect("ratex-parser should accept test input");
        super::expr(&parsed).map(|expression| Latex(expression).to_string())
    }

    #[test]
    fn parses_literals_variables_and_annotations() {
        expect!["42\nx\n\\hat{x}_{i}^{\\prime}\n\\tilde{x}\n\\vec{x}"].assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}",
            round_trip("42").unwrap(),
            round_trip("x").unwrap(),
            round_trip(r"\hat{x}_{i}^{\prime}").unwrap(),
            round_trip(r"\tilde{x}").unwrap(),
            round_trip(r"\vec{x}").unwrap(),
        ));
    }

    #[test]
    fn parses_holes() {
        expect![r"\square"].assert_eq(&round_trip(r"\square").unwrap());
    }

    #[test]
    fn parses_types_and_membership_atomically() {
        expect![
            "\\mathbb{B}\n\\mathbb{N}\n\\mathbb{Z}\n\\mathbb{R}\n\\mathbb{R}^{3}\n\\mathbb{R}^{3 \\times 4}\nA \\in \\mathbb{R}^{2 \\times 3}"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}\n{}\n{}",
            round_trip(r"\mathbb{B}").unwrap(),
            round_trip(r"\mathbb{N}").unwrap(),
            round_trip(r"\mathbb{Z}").unwrap(),
            round_trip(r"\mathbb{R}").unwrap(),
            round_trip(r"\mathbb{R}^{3}").unwrap(),
            round_trip(r"\mathbb{R}^{3 \times 4}").unwrap(),
            round_trip(r"A \in \mathbb{R}^{2 \times 3}").unwrap(),
        ));

        let parsed = parse(r"A \in \mathbb{R}^{2 \times 3}").unwrap();
        let expression = super::expr(&parsed).unwrap();
        assert!(matches!(
            &expression.raw,
            RawExpr::Binop(Binop::ElementOf, left, right)
                if matches!(left.raw, RawExpr::Variable(_))
                    && matches!(right.raw, RawExpr::Type(Type::Matrix(2, 3)))
        ));
    }

    #[test]
    fn one_by_one_matrix_type_canonicalizes_to_real() {
        let expression: Expr<()> = Expr::new(RawExpr::Type(Type::Matrix(1, 1)));
        let parsed = parse(&expression.as_latex().to_string()).unwrap();
        assert!(matches!(
            super::expr(&parsed).unwrap().raw,
            RawExpr::Type(Type::Real)
        ));
    }

    #[test]
    fn parses_binary_and_ternary_operators() {
        expect!["\\frac{1}{2}\nx^{2}\nx^{-1}\nx_{1}\nA_{1,2}\n\\langle x, y \\rangle"].assert_eq(
            &format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                round_trip(r"\frac{1}{2}").unwrap(),
                round_trip("x^{2}").unwrap(),
                round_trip("x^{-1}").unwrap(),
                round_trip("x_{1}").unwrap(),
                round_trip("A_{1,2}").unwrap(),
                round_trip(r"\langle x, y \rangle").unwrap(),
            ),
        );
    }

    #[test]
    fn parses_matrices() {
        expect![
            "\\begin{bmatrix}1 & x + y \\\\ \\frac{1}{2} & z^{2}\\end{bmatrix}\n\\begin{bmatrix}\\end{bmatrix}"
        ]
        .assert_eq(&format!(
            "{}\n{}",
            round_trip(
                r"\begin{bmatrix}1 & x + y \\ \frac{1}{2} & z^{2}\end{bmatrix}"
            )
            .unwrap(),
            round_trip(r"\begin{bmatrix}\end{bmatrix}").unwrap(),
        ));

        let parsed =
            parse(r"\begin{bmatrix}1 & x + y \\ \frac{1}{2} & z^{2}\end{bmatrix}").unwrap();
        let expression = super::expr(&parsed).unwrap();
        let crate::RawExpr::Matrix(matrix) = &expression.raw else {
            panic!("expected a matrix expression");
        };
        assert_eq!(matrix.rows, 2);
        assert_eq!(matrix.cols, 2);
        assert_eq!(matrix.elements.len(), 4);
        assert!(matches!(
            matrix.elements[0].raw,
            crate::RawExpr::NatLiteral(1)
        ));
        assert!(matches!(
            matrix.elements[1].raw,
            crate::RawExpr::Finop(crate::Finop::Plus, _)
        ));
        assert!(matches!(
            matrix.elements[2].raw,
            crate::RawExpr::Binop(crate::Binop::Div, _, _)
        ));
        assert!(matches!(
            matrix.elements[3].raw,
            crate::RawExpr::Binop(crate::Binop::Power, _, _)
        ));
    }

    #[test]
    fn parses_unary_and_finite_operators() {
        expect![
            "\\operatorname{tr}(x)\n\\operatorname{det}(x)\n\\left\\lVert x \\right\\rVert_{1}\n\\left\\lVert x \\right\\rVert_{2}\n\\left\\lVert x \\right\\rVert_{\\infty}\n\\left\\lVert x \\right\\rVert_{F}\n\\max(1, 2)\n\\min(1, 2)"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
            round_trip(r"\operatorname{tr}(x)").unwrap(),
            round_trip(r"\operatorname{det}(x)").unwrap(),
            round_trip(r"\left\lVert x \right\rVert_{1}").unwrap(),
            round_trip(r"\left\lVert x \right\rVert_{2}").unwrap(),
            round_trip(r"\left\lVert x \right\rVert_{\infty}").unwrap(),
            round_trip(r"\left\lVert x \right\rVert_{F}").unwrap(),
            round_trip(r"\max(1, 2)").unwrap(),
            round_trip(r"\min(1, 2)").unwrap(),
        ));
    }

    #[test]
    fn parses_precedence_and_subtraction() {
        expect![
            "x + y z\n\\left(x + y\\right) z\n\\left(x + y\\right)^{2}\n-\\left(x + y\\right)\nx - y\nx \\left(-y\\right)"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}\n{}",
            round_trip("x + y z").unwrap(),
            round_trip(r"\left(x + y\right) z").unwrap(),
            round_trip(r"\left(x + y\right)^{2}").unwrap(),
            round_trip(r"-\left(x + y\right)").unwrap(),
            round_trip("x - y").unwrap(),
            round_trip(r"x \left(-y\right)").unwrap(),
        ));
    }

    #[test]
    fn parses_comparison_and_logic_chains() {
        expect!["a = b < c > d \\le e \\ge f\nP \\implies Q \\iff R\na + b < c d \\implies P"]
            .assert_eq(&format!(
                "{}\n{}\n{}",
                round_trip(r"a = b < c > d \le e \ge f").unwrap(),
                round_trip(r"P \implies Q \iff R").unwrap(),
                round_trip(r"a + b < c d \implies P").unwrap(),
            ));
    }

    #[test]
    fn parses_sequence_operators() {
        expect![
            "\\sum_{i=1}^{3}i\n\\prod_{i=1}^{3}i\n\\sum_{i=1}^{3}\\left(x + y\\right)\n\\sum_{i=1}^{3}\\left(x = y\\right)\n\\sum_{i=1}^{3}\\left(P \\implies Q\\right)\n\\sum_{i=1}^{3}x y"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}\n{}",
            round_trip(r"\sum_{i=1}^{3}i").unwrap(),
            round_trip(r"\prod_{i=1}^{3}i").unwrap(),
            round_trip(r"\sum_{i=1}^{3}\left(x + y\right)").unwrap(),
            round_trip(r"\sum_{i=1}^{3}\left(x = y\right)").unwrap(),
            round_trip(r"\sum_{i=1}^{3}\left(P \implies Q\right)").unwrap(),
            round_trip(r"\sum_{i=1}^{3}x y").unwrap(),
        ));

        let parsed = parse(r"\sum_{i=1}^{3}x y").unwrap();
        let sequence = super::expr(&parsed).unwrap();
        assert!(matches!(
            &sequence.raw,
            crate::RawExpr::Seqop(
                _,
                _,
                body
            ) if matches!(&body.raw, crate::RawExpr::Finop(crate::Finop::Times, factors) if factors.len() == 2)
        ));
    }

    #[test]
    fn reports_empty_malformed_and_unsupported_input() {
        assert!(matches!(
            super::expr(&[]),
            Err(FromTexError::EmptyExpression)
        ));

        let dangling = parse("x +").unwrap();
        assert!(matches!(
            super::expr(&dangling),
            Err(FromTexError::UnexpectedEnd { .. })
        ));

        let unsupported = parse(r"\sqrt{x}").unwrap();
        assert!(matches!(
            super::expr(&unsupported),
            Err(FromTexError::Unsupported { .. })
        ));

        let trailing = parse("x, y").unwrap();
        assert!(matches!(
            super::expr(&trailing),
            Err(FromTexError::TrailingNodes { .. })
        ));

        let ragged = parse(r"\begin{bmatrix}1 & 2 \\ 3\end{bmatrix}").unwrap();
        assert!(matches!(
            super::expr(&ragged),
            Err(FromTexError::Malformed { .. })
        ));

        let wrong_matrix_delimiter = parse(r"\begin{pmatrix}1 & 2 \\ 3 & 4\end{pmatrix}").unwrap();
        assert!(matches!(
            super::expr(&wrong_matrix_delimiter),
            Err(FromTexError::Unsupported { .. })
        ));

        let symbolic_type_dimension = parse(r"\mathbb{R}^{n}").unwrap();
        assert!(matches!(
            super::expr(&symbolic_type_dimension),
            Err(FromTexError::Malformed { .. })
        ));

        let too_many_type_dimensions = parse(r"\mathbb{R}^{2 \times 3 \times 4}").unwrap();
        assert!(matches!(
            super::expr(&too_many_type_dimensions),
            Err(FromTexError::Malformed { .. })
        ));
    }
}
