use std::fmt;

use crate::{
    Binop, Cmp, CmpChain, Expr, Finop, Logic, LogicChain, Matrix, Monop, SeqOp, Triop, Type,
    Variable,
};

impl<Metadata> fmt::Display for AsLatex<Metadata> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        expr(f, &self.e)
    }
}

pub struct AsLatex<Metadata> {
    e: Expr<Metadata>,
}

impl<Metadata> Expr<Metadata> {
    pub fn as_latex(&self) -> AsLatex<Metadata> {
        AsLatex { e: self.clone() }
    }
}

pub fn expr<Metadata>(f: &mut fmt::Formatter<'_>, e: &Expr<Metadata>) -> fmt::Result {
    match &e.raw {
        crate::RawExpr::Hole => write!(f, r"\square"),
        crate::RawExpr::Type(ty) => type_expr(f, ty),
        crate::RawExpr::Variable(v) => variable(f, v),
        crate::RawExpr::NatLiteral(value) => write!(f, "{value}"),
        crate::RawExpr::Matrix(value) => matrix(f, value),
        crate::RawExpr::Monop(op, e) => monop(f, op, |f| {
            let grouped = match op {
                Monop::Neg => precedence(e) <= Precedence::Addition,
                Monop::Inverse => precedence(e) < Precedence::Power,
                _ => false,
            };
            grouped_expr(f, e, grouped)
        }),
        crate::RawExpr::Binop(op, e0, e1) => binop(
            f,
            op,
            |f| {
                grouped_expr(
                    f,
                    e0,
                    (matches!(op, Binop::Power) && precedence(e0) < Precedence::Power)
                        || (matches!(op, Binop::ElementOf)
                            && precedence(e0) <= Precedence::Comparison),
                )
            },
            |f| {
                grouped_expr(
                    f,
                    e1,
                    matches!(op, Binop::ElementOf) && precedence(e1) <= Precedence::Comparison,
                )
            },
        ),
        crate::RawExpr::Triop(op, e0, e1, e2) => {
            triop(f, op, |f| expr(f, e0), |f| expr(f, e1), |f| expr(f, e2))
        }
        crate::RawExpr::Finop(op, exprs) => finop(f, op, exprs.iter()),
        crate::RawExpr::CmpChain(chain) => cmp_chain(f, chain),
        crate::RawExpr::LogicChain(chain) => logic_chain(f, chain),
        crate::RawExpr::Seqop(op, range, body) => seqop(
            f,
            op,
            &range.index_variable.name,
            |f| expr(f, &range.from),
            |f| expr(f, &range.to),
            |f| grouped_expr(f, body, precedence(body) <= Precedence::Addition),
        ),
    }
}

fn matrix<Metadata>(f: &mut fmt::Formatter<'_>, matrix: &Matrix<Expr<Metadata>>) -> fmt::Result {
    let expected_elements = matrix
        .rows
        .checked_mul(matrix.cols)
        .expect("matrix dimensions overflow usize");
    assert_eq!(
        matrix.elements.len(),
        expected_elements,
        "matrix element count does not match its dimensions"
    );
    assert!(
        (matrix.rows == 0) == (matrix.cols == 0),
        "matrix dimensions must both be zero or both be nonzero"
    );

    write!(f, r"\begin{{bmatrix}}")?;
    for row in 0..matrix.rows {
        if row > 0 {
            write!(f, r" \\ ")?;
        }
        for column in 0..matrix.cols {
            if column > 0 {
                write!(f, " & ")?;
            }
            expr(f, &matrix.at(row, column))?;
        }
    }
    write!(f, r"\end{{bmatrix}}")
}

fn grouped_expr<Metadata>(
    f: &mut fmt::Formatter<'_>,
    e: &Expr<Metadata>,
    grouped: bool,
) -> fmt::Result {
    if grouped {
        write!(f, r"\left(")?;
    }
    expr(f, e)?;
    if grouped {
        write!(f, r"\right)")?;
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Logic,
    Comparison,
    Addition,
    Multiplication,
    Prefix,
    Power,
    Atom,
}

fn precedence<Metadata>(e: &Expr<Metadata>) -> Precedence {
    match &e.raw {
        crate::RawExpr::LogicChain(_) => Precedence::Logic,
        crate::RawExpr::CmpChain(_) | crate::RawExpr::Binop(Binop::ElementOf, _, _) => {
            Precedence::Comparison
        }
        crate::RawExpr::Finop(Finop::Plus, _) => Precedence::Addition,
        crate::RawExpr::Finop(Finop::Times, _) => Precedence::Multiplication,
        crate::RawExpr::Monop(Monop::Neg, _) => Precedence::Prefix,
        crate::RawExpr::Monop(Monop::Inverse, _) | crate::RawExpr::Binop(Binop::Power, _, _) => {
            Precedence::Power
        }
        _ => Precedence::Atom,
    }
}

fn type_expr(f: &mut fmt::Formatter<'_>, ty: &Type) -> fmt::Result {
    match ty {
        Type::Bool => write!(f, r"\mathbb{{B}}"),
        Type::Nat => write!(f, r"\mathbb{{N}}"),
        Type::Int => write!(f, r"\mathbb{{Z}}"),
        Type::Real | Type::Matrix(1, 1) => write!(f, r"\mathbb{{R}}"),
        Type::Matrix(rows, 1) => write!(f, r"\mathbb{{R}}^{{{rows}}}"),
        Type::Matrix(rows, cols) => {
            write!(f, r"\mathbb{{R}}^{{{rows} \times {cols}}}")
        }
    }
}

fn variable(f: &mut fmt::Formatter<'_>, v: &Variable) -> fmt::Result {
    let mut name = v.name.clone();

    for annotation in &v.annotations {
        name = match annotation {
            crate::Annotation::Hat => format!(r"\hat{{{name}}}"),
            crate::Annotation::Tilde => format!(r"\tilde{{{name}}}"),
            crate::Annotation::Arrow => format!(r"\vec{{{name}}}"),
            crate::Annotation::Prime => name,
        };
    }

    write!(f, "{name}")?;
    if !v.non_numeric_subscript.is_empty() {
        write!(f, "_{{{}}}", v.non_numeric_subscript)?;
    }
    for annotation in &v.annotations {
        if matches!(annotation, crate::Annotation::Prime) {
            write!(f, r"^{{\prime}}")?;
        }
    }
    Ok(())
}

fn monop<F: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result>(
    f: &mut fmt::Formatter<'_>,
    op: &Monop,
    e: F,
) -> fmt::Result {
    match op {
        Monop::Trace => write!(f, r"\operatorname{{tr}}(")?,
        Monop::Det => write!(f, r"\operatorname{{det}}(")?,
        Monop::Neg => write!(f, "-")?,
        Monop::Inverse => {}
        Monop::Norm1 | Monop::Norm2 | Monop::NormInfty | Monop::NormFrob => {
            write!(f, r"\left\lVert ")?
        }
    }

    e(f)?;

    match op {
        Monop::Trace | Monop::Det => write!(f, ")"),
        Monop::Neg => Ok(()),
        Monop::Inverse => write!(f, "^{{-1}}"),
        Monop::Norm1 => write!(f, r" \right\rVert_{{1}}"),
        Monop::Norm2 => write!(f, r" \right\rVert_{{2}}"),
        Monop::NormInfty => write!(f, r" \right\rVert_{{\infty}}"),
        Monop::NormFrob => write!(f, r" \right\rVert_{{F}}"),
    }
}

fn binop<
    F0: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    F1: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
>(
    f: &mut fmt::Formatter<'_>,
    op: &Binop,
    e0: F0,
    e1: F1,
) -> fmt::Result {
    match op {
        Binop::Div => {
            write!(f, r"\frac{{")?;
            e0(f)?;
            write!(f, "}}{{")?;
            e1(f)?;
            write!(f, "}}")
        }
        Binop::Power => {
            e0(f)?;
            write!(f, "^{{")?;
            e1(f)?;
            write!(f, "}}")
        }
        Binop::InnerProd => {
            write!(f, r"\langle ")?;
            e0(f)?;
            write!(f, ", ")?;
            e1(f)?;
            write!(f, r" \rangle")
        }
        Binop::ElementOf => {
            e0(f)?;
            write!(f, r" \in ")?;
            e1(f)
        }
        Binop::SingleSubscript => {
            e0(f)?;
            write!(f, "_{{")?;
            e1(f)?;
            write!(f, "}}")
        }
    }
}

fn triop<
    F0: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    F1: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    F2: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
>(
    f: &mut fmt::Formatter<'_>,
    op: &Triop,
    e0: F0,
    e1: F1,
    e2: F2,
) -> fmt::Result {
    match op {
        Triop::DoubleSubscript => {
            e0(f)?;
            write!(f, "_{{")?;
            e1(f)?;
            write!(f, ",")?;
            e2(f)?;
            write!(f, "}}")
        }
    }
}

fn finop<'a, Metadata: 'a, I>(f: &mut fmt::Formatter<'_>, op: &Finop, exprs: I) -> fmt::Result
where
    I: IntoIterator<Item = &'a Expr<Metadata>>,
{
    match op {
        Finop::Max => write!(f, r"\max(")?,
        Finop::Min => write!(f, r"\min(")?,
        _ => {}
    }

    for (index, expression) in exprs.into_iter().enumerate() {
        if let (Finop::Plus, crate::RawExpr::Monop(Monop::Neg, inner)) = (op, &expression.raw)
            && index > 0
        {
            write!(f, " - ")?;
            grouped_expr(f, inner, precedence(inner) <= Precedence::Addition)?;
            continue;
        }

        if index > 0 {
            write!(f, "{}", finop_separator(op))?;
        }
        grouped_expr(
            f,
            expression,
            matches!(op, Finop::Times)
                && (precedence(expression) < Precedence::Multiplication
                    || matches!(&expression.raw, crate::RawExpr::Monop(Monop::Neg, _))),
        )?;
    }

    match op {
        Finop::Max | Finop::Min => write!(f, ")"),
        _ => Ok(()),
    }
}

fn cmp_chain<Metadata>(f: &mut fmt::Formatter<'_>, chain: &CmpChain<Metadata>) -> fmt::Result {
    grouped_expr(
        f,
        &chain.start,
        precedence(&chain.start) <= Precedence::Comparison,
    )?;
    for (op, expression) in &chain.assertions {
        write!(f, " {} ", cmp_symbol(op))?;
        grouped_expr(
            f,
            expression,
            precedence(expression) <= Precedence::Comparison,
        )?;
    }
    Ok(())
}

fn logic_chain<Metadata>(f: &mut fmt::Formatter<'_>, chain: &LogicChain<Metadata>) -> fmt::Result {
    grouped_expr(
        f,
        &chain.start,
        precedence(&chain.start) <= Precedence::Logic,
    )?;
    for (op, expression) in &chain.assertions {
        write!(f, " {} ", logic_symbol(op))?;
        grouped_expr(f, expression, precedence(expression) <= Precedence::Logic)?;
    }
    Ok(())
}

fn cmp_symbol(op: &Cmp) -> &'static str {
    match op {
        Cmp::Eq => "=",
        Cmp::Ne => r"\ne",
        Cmp::Lt => "<",
        Cmp::Gt => ">",
        Cmp::Le => r"\le",
        Cmp::Ge => r"\ge",
    }
}

fn logic_symbol(op: &Logic) -> &'static str {
    match op {
        Logic::Iff => r"\iff",
        Logic::Imp => r"\implies",
    }
}

fn seqop<
    F0: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    F1: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    F2: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
>(
    f: &mut fmt::Formatter<'_>,
    op: &SeqOp,
    index_variable: &str,
    from: F0,
    to: F1,
    e: F2,
) -> fmt::Result {
    match op {
        SeqOp::Sum => write!(f, r"\sum")?,
        SeqOp::Prod => write!(f, r"\prod")?,
    }
    write!(f, "_{{{index_variable}=")?;
    from(f)?;
    write!(f, "}}^{{")?;
    to(f)?;
    write!(f, "}}")?;
    e(f)
}

fn finop_separator(op: &Finop) -> &'static str {
    match op {
        Finop::Plus => " + ",
        Finop::Times => " ",
        Finop::Max | Finop::Min => ", ",
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::{
        Annotation, Binop, Cmp, CmpChain, Expr, Finop, Logic, LogicChain, Matrix, Monop, RawExpr,
        SeqOp, SeqopRange, Triop, Type, Variable,
    };

    fn as_latex(raw: RawExpr<()>) -> String {
        Expr::new(raw).as_latex().to_string()
    }

    #[test]
    fn test_nat_literal() {
        expect!["42"].assert_eq(&as_latex(RawExpr::NatLiteral(42)));
    }

    #[test]
    fn test_hole() {
        expect![r"\square"].assert_eq(&as_latex(RawExpr::Hole));
    }

    #[test]
    fn test_types_and_membership() {
        let rendered_types = [
            Type::Bool,
            Type::Nat,
            Type::Int,
            Type::Real,
            Type::Matrix(3, 1),
            Type::Matrix(3, 4),
            Type::Matrix(1, 1),
        ]
        .map(|ty| as_latex(RawExpr::Type(ty)))
        .join("\n");
        expect![
            "\\mathbb{B}\n\\mathbb{N}\n\\mathbb{Z}\n\\mathbb{R}\n\\mathbb{R}^{3}\n\\mathbb{R}^{3 \\times 4}\n\\mathbb{R}"
        ]
        .assert_eq(&rendered_types);

        expect!["A \\in \\mathbb{R}^{2 \\times 3}"].assert_eq(&as_latex(RawExpr::Binop(
            Binop::ElementOf,
            variable_expr("A"),
            Expr::new(RawExpr::Type(Type::Matrix(2, 3))),
        )));
    }

    #[test]
    fn test_matrix() {
        let matrix = || Matrix {
            rows: 2,
            cols: 2,
            elements: vec![
                Expr::new(RawExpr::NatLiteral(1)),
                Expr::new(RawExpr::Finop(
                    Finop::Plus,
                    vec![variable_expr("x"), variable_expr("y")],
                )),
                Expr::new(RawExpr::Binop(
                    Binop::Div,
                    Expr::new(RawExpr::NatLiteral(1)),
                    Expr::new(RawExpr::NatLiteral(2)),
                )),
                Expr::new(RawExpr::Binop(
                    Binop::Power,
                    variable_expr("z"),
                    Expr::new(RawExpr::NatLiteral(2)),
                )),
            ],
        };

        expect![
            "\\begin{bmatrix}1 & x + y \\\\ \\frac{1}{2} & z^{2}\\end{bmatrix}\nx \\begin{bmatrix}1 & x + y \\\\ \\frac{1}{2} & z^{2}\\end{bmatrix}\n\\begin{bmatrix}1 & x + y \\\\ \\frac{1}{2} & z^{2}\\end{bmatrix}^{2}"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}",
            as_latex(RawExpr::Matrix(matrix())),
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![variable_expr("x"), Expr::new(RawExpr::Matrix(matrix()))],
            )),
            as_latex(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Matrix(matrix())),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
        ));
    }

    #[test]
    #[should_panic(expected = "matrix element count does not match its dimensions")]
    fn test_matrix_rejects_bad_element_count() {
        as_latex(RawExpr::Matrix(Matrix {
            rows: 2,
            cols: 2,
            elements: vec![Expr::new(RawExpr::NatLiteral(1))],
        }));
    }

    #[test]
    #[should_panic(expected = "matrix dimensions overflow usize")]
    fn test_matrix_rejects_overflowing_dimensions() {
        as_latex(RawExpr::Matrix(Matrix {
            rows: usize::MAX,
            cols: 2,
            elements: Vec::new(),
        }));
    }

    #[test]
    #[should_panic(expected = "matrix dimensions must both be zero or both be nonzero")]
    fn test_matrix_rejects_one_zero_dimension() {
        as_latex(RawExpr::Matrix(Matrix {
            rows: 0,
            cols: 2,
            elements: Vec::new(),
        }));
    }

    #[test]
    fn test_variable() {
        expect!["x"].assert_eq(&as_latex(RawExpr::Variable(Variable {
            name: "x".to_owned(),
            non_numeric_subscript: String::new(),
            annotations: Vec::new(),
        })));
    }

    #[test]
    fn test_annotated_variable() {
        expect!["\\hat{x}_{i}^{\\prime}"].assert_eq(&as_latex(RawExpr::Variable(Variable {
            name: "x".to_owned(),
            non_numeric_subscript: "i".to_owned(),
            annotations: vec![Annotation::Hat, Annotation::Prime],
        })));
    }

    #[test]
    fn test_div() {
        expect!["\\frac{1}{0}"].assert_eq(&as_latex(RawExpr::Binop(
            Binop::Div,
            Expr::new(RawExpr::NatLiteral(1)),
            Expr::new(RawExpr::NatLiteral(0)),
        )))
    }

    #[test]
    fn test_other_binary_operators() {
        expect!["x^{2}\n\\langle x, y \\rangle\nx_{1}"].assert_eq(&format!(
            "{}\n{}\n{}",
            as_latex(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
            as_latex(RawExpr::Binop(
                Binop::InnerProd,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
                Expr::new(RawExpr::Variable(Variable::new("y"))),
            )),
            as_latex(RawExpr::Binop(
                Binop::SingleSubscript,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
                Expr::new(RawExpr::NatLiteral(1)),
            )),
        ));
    }

    #[test]
    fn test_unary_operators() {
        expect!["\\operatorname{tr}(x)\n\\operatorname{det}(x)\n-x\nx^{-1}"].assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Monop(
                Monop::Trace,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Det,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Neg,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Inverse,
                Expr::new(RawExpr::Variable(Variable::new("x"))),
            )),
        ));
    }

    #[test]
    fn test_norm_operators() {
        let x = || Expr::new(RawExpr::Variable(Variable::new("x")));

        expect![
            "\\left\\lVert x \\right\\rVert_{1}\n\\left\\lVert x \\right\\rVert_{2}\n\\left\\lVert x \\right\\rVert_{\\infty}\n\\left\\lVert x \\right\\rVert_{F}"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Monop(Monop::Norm1, x())),
            as_latex(RawExpr::Monop(Monop::Norm2, x())),
            as_latex(RawExpr::Monop(Monop::NormInfty, x())),
            as_latex(RawExpr::Monop(Monop::NormFrob, x())),
        ));
    }

    #[test]
    fn test_double_subscript() {
        expect!["A_{1,2}"].assert_eq(&as_latex(RawExpr::Triop(
            Triop::DoubleSubscript,
            Expr::new(RawExpr::Variable(Variable::new("A"))),
            Expr::new(RawExpr::NatLiteral(1)),
            Expr::new(RawExpr::NatLiteral(2)),
        )));
    }

    #[test]
    fn test_finite_operators() {
        let values = vec![
            Expr::new(RawExpr::NatLiteral(1)),
            Expr::new(RawExpr::NatLiteral(2)),
        ];
        let factors = vec![variable_expr("x"), variable_expr("y")];

        expect!["1 + 2\nx y\n\\max(1, 2)\n\\min(1, 2)"].assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Finop(Finop::Plus, values.clone())),
            as_latex(RawExpr::Finop(Finop::Times, factors)),
            as_latex(RawExpr::Finop(Finop::Max, values.clone())),
            as_latex(RawExpr::Finop(Finop::Min, values)),
        ));
    }

    #[test]
    fn test_sequence_operators() {
        let sequence = |op| {
            RawExpr::Seqop(
                op,
                SeqopRange {
                    index_variable: Variable::new("i"),
                    from: Expr::new(RawExpr::NatLiteral(1)),
                    to: Expr::new(RawExpr::NatLiteral(3)),
                },
                Expr::new(RawExpr::Variable(Variable::new("i"))),
            )
        };

        expect!["\\sum_{i=1}^{3}i\n\\prod_{i=1}^{3}i"].assert_eq(&format!(
            "{}\n{}",
            as_latex(sequence(SeqOp::Sum)),
            as_latex(sequence(SeqOp::Prod)),
        ));
    }

    #[test]
    fn test_sequence_body_grouping() {
        let sequence = |body| {
            RawExpr::Seqop(
                SeqOp::Sum,
                SeqopRange {
                    index_variable: Variable::new("i"),
                    from: Expr::new(RawExpr::NatLiteral(1)),
                    to: Expr::new(RawExpr::NatLiteral(3)),
                },
                body,
            )
        };

        expect![
            "\\sum_{i=1}^{3}\\left(x + y\\right)\n\\sum_{i=1}^{3}\\left(x = y\\right)\n\\sum_{i=1}^{3}\\left(P \\implies Q\\right)\n\\sum_{i=1}^{3}x y"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(sequence(Expr::new(RawExpr::Finop(
                Finop::Plus,
                vec![variable_expr("x"), variable_expr("y")],
            )))),
            as_latex(sequence(Expr::new(RawExpr::CmpChain(CmpChain {
                start: variable_expr("x"),
                assertions: vec![(Cmp::Eq, variable_expr("y"))],
            })))),
            as_latex(sequence(Expr::new(RawExpr::LogicChain(LogicChain {
                start: variable_expr("P"),
                assertions: vec![(Logic::Imp, variable_expr("Q"))],
            })))),
            as_latex(sequence(Expr::new(RawExpr::Finop(
                Finop::Times,
                vec![variable_expr("x"), variable_expr("y")],
            )))),
        ));
    }

    #[test]
    fn test_grouping_for_ambiguous_operands() {
        let sum = || {
            Expr::new(RawExpr::Finop(
                Finop::Plus,
                vec![variable_expr("x"), variable_expr("y")],
            ))
        };

        expect![
            "\\left(x + y\\right) z\n\\left(x + y\\right)^{2}\n-\\left(x + y\\right)\n\\left(x + y\\right)^{-1}\nx \\left(-y\\right)"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}",
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![sum(), variable_expr("z")],
            )),
            as_latex(RawExpr::Binop(
                Binop::Power,
                sum(),
                Expr::new(RawExpr::NatLiteral(2)),
            )),
            as_latex(RawExpr::Monop(Monop::Neg, sum())),
            as_latex(RawExpr::Monop(Monop::Inverse, sum())),
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![
                    variable_expr("x"),
                    Expr::new(RawExpr::Monop(Monop::Neg, variable_expr("y"))),
                ],
            )),
        ));
    }

    #[test]
    fn test_associative_operators_do_not_add_grouping() {
        expect!["x + y + z\nx y z"].assert_eq(&format!(
            "{}\n{}",
            as_latex(RawExpr::Finop(
                Finop::Plus,
                vec![
                    variable_expr("x"),
                    Expr::new(RawExpr::Finop(
                        Finop::Plus,
                        vec![variable_expr("y"), variable_expr("z")],
                    )),
                ],
            )),
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![
                    variable_expr("x"),
                    Expr::new(RawExpr::Finop(
                        Finop::Times,
                        vec![variable_expr("y"), variable_expr("z")],
                    )),
                ],
            )),
        ));
    }

    #[test]
    fn test_addition_of_negated_terms_uses_subtraction() {
        expect!["x - y\nx - \\left(y + z\\right)"].assert_eq(&format!(
            "{}\n{}",
            as_latex(RawExpr::Finop(
                Finop::Plus,
                vec![
                    variable_expr("x"),
                    Expr::new(RawExpr::Monop(Monop::Neg, variable_expr("y"))),
                ],
            )),
            as_latex(RawExpr::Finop(
                Finop::Plus,
                vec![
                    variable_expr("x"),
                    Expr::new(RawExpr::Monop(
                        Monop::Neg,
                        Expr::new(RawExpr::Finop(
                            Finop::Plus,
                            vec![variable_expr("y"), variable_expr("z")],
                        )),
                    )),
                ],
            )),
        ));
    }

    fn variable_expr(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }
    #[test]
    fn test_cmp_chain() {
        expect!["b + b + a = 2 b + a = b + a + b\na = b < c > d \\le e \\ge f"].assert_eq(
            &format!(
                "{}\n{}",
                as_latex(RawExpr::CmpChain(CmpChain {
                    start: Expr::new(RawExpr::Finop(
                        Finop::Plus,
                        vec![variable_expr("b"), variable_expr("b"), variable_expr("a")],
                    )),
                    assertions: vec![
                        (
                            Cmp::Eq,
                            Expr::new(RawExpr::Finop(
                                Finop::Plus,
                                vec![
                                    Expr::new(RawExpr::Finop(
                                        Finop::Times,
                                        vec![Expr::new(RawExpr::NatLiteral(2)), variable_expr("b")],
                                    )),
                                    variable_expr("a"),
                                ],
                            )),
                        ),
                        (
                            Cmp::Eq,
                            Expr::new(RawExpr::Finop(
                                Finop::Plus,
                                vec![variable_expr("b"), variable_expr("a"), variable_expr("b")],
                            )),
                        ),
                    ],
                })),
                as_latex(RawExpr::CmpChain(CmpChain {
                    start: variable_expr("a"),
                    assertions: vec![
                        (Cmp::Eq, variable_expr("b")),
                        (Cmp::Lt, variable_expr("c")),
                        (Cmp::Gt, variable_expr("d")),
                        (Cmp::Le, variable_expr("e")),
                        (Cmp::Ge, variable_expr("f")),
                    ],
                })),
            ),
        );
        expect![r"a \ne b"].assert_eq(&as_latex(RawExpr::CmpChain(CmpChain {
            start: variable_expr("a"),
            assertions: vec![(Cmp::Ne, variable_expr("b"))],
        })));
    }

    #[test]
    fn test_logic_chain() {
        expect!["P \\implies Q \\iff R"].assert_eq(&as_latex(RawExpr::LogicChain(LogicChain {
            start: variable_expr("P"),
            assertions: vec![
                (Logic::Imp, variable_expr("Q")),
                (Logic::Iff, variable_expr("R")),
            ],
        })))
    }
}
