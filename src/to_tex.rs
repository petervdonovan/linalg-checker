use std::fmt;

use crate::{Binop, Expr, Finop, Monop, SeqOp, Triop};

impl<Metadata> fmt::Display for AsLatex<Metadata> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        expr(f, &self.e)
    }
}

pub struct AsLatex<Metadata> {
    e: Expr<Metadata>,
}

pub fn expr<Metadata>(f: &mut fmt::Formatter<'_>, e: &Expr<Metadata>) -> fmt::Result {
    match &e.raw {
        crate::RawExpr::Variable(variable) => {
            let mut name = variable.name.clone();

            for annotation in &variable.annotations {
                name = match annotation {
                    crate::Annotation::Hat => format!(r"\hat{{{name}}}"),
                    crate::Annotation::Tilde => format!(r"\tilde{{{name}}}"),
                    crate::Annotation::Arrow => format!(r"\vec{{{name}}}"),
                    crate::Annotation::Prime => name,
                };
            }

            write!(f, "{name}")?;
            if !variable.non_numeric_subscript.is_empty() {
                write!(f, "_{{{}}}", variable.non_numeric_subscript)?;
            }
            for annotation in &variable.annotations {
                if matches!(annotation, crate::Annotation::Prime) {
                    write!(f, r"^{{\prime}}")?;
                }
            }
            Ok(())
        }
        crate::RawExpr::NatLiteral(value) => write!(f, "{value}"),
        crate::RawExpr::Monop(op, e) => monop(f, op, |f| expr(f, e)),
        crate::RawExpr::Binop(op, e0, e1) => binop(f, op, |f| expr(f, e0), |f| expr(f, e1)),
        crate::RawExpr::Triop(op, e0, e1, e2) => {
            triop(f, op, |f| expr(f, e0), |f| expr(f, e1), |f| expr(f, e2))
        }
        crate::RawExpr::Finop(op, exprs) => finop(f, op, |f| {
            for (index, expression) in exprs.iter().enumerate() {
                if index > 0 {
                    write!(f, "{}", finop_separator(op))?;
                }
                expr(f, expression)?;
            }
            Ok(())
        }),
        crate::RawExpr::Seqop(op, range, body) => {
            let seq_op = match op {
                Finop::Plus => SeqOp::Sum,
                Finop::Times => SeqOp::Prod,
                _ => return expr(f, body),
            };
            seqop(
                f,
                &seq_op,
                &range.index_variable.name,
                |f| expr(f, &range.from),
                |f| expr(f, &range.to),
                |f| expr(f, body),
            )
        }
    }
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

fn finop<F: FnMut(&mut fmt::Formatter<'_>) -> fmt::Result>(
    f: &mut fmt::Formatter<'_>,
    op: &Finop,
    mut exprs: F,
) -> fmt::Result {
    match op {
        Finop::Max => write!(f, r"\max(")?,
        Finop::Min => write!(f, r"\min(")?,
        _ => {}
    }
    exprs(f)?;
    match op {
        Finop::Max | Finop::Min => write!(f, ")"),
        _ => Ok(()),
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
        Finop::Times => r" \cdot ",
        Finop::LogicChain => r" \implies ",
        Finop::CmpChain => " = ",
        Finop::Max | Finop::Min => ", ",
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use expect_test::expect;

    use crate::{
        to_tex::AsLatex, Annotation, Binop, Finop, MetaExpr, Monop, RawExpr, SeqopRange, Triop,
        Variable,
    };

    fn expr(raw: RawExpr<()>) -> Rc<MetaExpr<()>> {
        Rc::new(MetaExpr { meta: (), raw })
    }

    fn as_latex(raw: RawExpr<()>) -> String {
        AsLatex { e: expr(raw) }.to_string()
    }

    #[test]
    fn test_nat_literal() {
        expect!["42"].assert_eq(&as_latex(RawExpr::NatLiteral(42)));
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
            expr(RawExpr::NatLiteral(1)),
            expr(RawExpr::NatLiteral(0)),
        )))
    }

    #[test]
    fn test_other_binary_operators() {
        expect!["x^{2}\n\\langle x, y \\rangle\nx_{1}"].assert_eq(&format!(
            "{}\n{}\n{}",
            as_latex(RawExpr::Binop(
                Binop::Power,
                expr(RawExpr::Variable(variable("x"))),
                expr(RawExpr::NatLiteral(2)),
            )),
            as_latex(RawExpr::Binop(
                Binop::InnerProd,
                expr(RawExpr::Variable(variable("x"))),
                expr(RawExpr::Variable(variable("y"))),
            )),
            as_latex(RawExpr::Binop(
                Binop::SingleSubscript,
                expr(RawExpr::Variable(variable("x"))),
                expr(RawExpr::NatLiteral(1)),
            )),
        ));
    }

    #[test]
    fn test_unary_operators() {
        expect!["\\operatorname{tr}(x)\n\\operatorname{det}(x)\n-x\nx^{-1}"].assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Monop(
                Monop::Trace,
                expr(RawExpr::Variable(variable("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Det,
                expr(RawExpr::Variable(variable("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Neg,
                expr(RawExpr::Variable(variable("x"))),
            )),
            as_latex(RawExpr::Monop(
                Monop::Inverse,
                expr(RawExpr::Variable(variable("x"))),
            )),
        ));
    }

    #[test]
    fn test_norm_operators() {
        let x = || expr(RawExpr::Variable(variable("x")));

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
            expr(RawExpr::Variable(variable("A"))),
            expr(RawExpr::NatLiteral(1)),
            expr(RawExpr::NatLiteral(2)),
        )));
    }

    #[test]
    fn test_finite_operators() {
        let values = vec![expr(RawExpr::NatLiteral(1)), expr(RawExpr::NatLiteral(2))];

        expect!["1 + 2\n1 \\cdot 2\n\\max(1, 2)\n\\min(1, 2)"].assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Finop(Finop::Plus, values.clone())),
            as_latex(RawExpr::Finop(Finop::Times, values.clone())),
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
                    index_variable: variable("i"),
                    from: expr(RawExpr::NatLiteral(1)),
                    to: expr(RawExpr::NatLiteral(3)),
                },
                expr(RawExpr::Variable(variable("i"))),
            )
        };

        expect!["\\sum_{i=1}^{3}i\n\\prod_{i=1}^{3}i"].assert_eq(&format!(
            "{}\n{}",
            as_latex(sequence(Finop::Plus)),
            as_latex(sequence(Finop::Times)),
        ));
    }

    #[test]
    fn test_grouping_for_ambiguous_operands() {
        let sum = || {
            expr(RawExpr::Finop(
                Finop::Plus,
                vec![variable_expr("x"), variable_expr("y")],
            ))
        };

        expect![
            "\\left(x + y\\right) \\cdot z\n\\left(x + y\\right)^{2}\n-\\left(x + y\\right)\n\\left(x + y\\right)^{-1}"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}",
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![sum(), variable_expr("z")],
            )),
            as_latex(RawExpr::Binop(
                Binop::Power,
                sum(),
                expr(RawExpr::NatLiteral(2)),
            )),
            as_latex(RawExpr::Monop(Monop::Neg, sum())),
            as_latex(RawExpr::Monop(Monop::Inverse, sum())),
        ));
    }

    #[test]
    fn test_associative_operators_do_not_add_grouping() {
        expect!["x + y + z\nx \\cdot y \\cdot z"].assert_eq(&format!(
            "{}\n{}",
            as_latex(RawExpr::Finop(
                Finop::Plus,
                vec![
                    variable_expr("x"),
                    expr(RawExpr::Finop(
                        Finop::Plus,
                        vec![variable_expr("y"), variable_expr("z")],
                    )),
                ],
            )),
            as_latex(RawExpr::Finop(
                Finop::Times,
                vec![
                    variable_expr("x"),
                    expr(RawExpr::Finop(
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
                    expr(RawExpr::Monop(Monop::Neg, variable_expr("y"))),
                ],
            )),
            as_latex(RawExpr::Finop(
                Finop::Plus,
                vec![
                    variable_expr("x"),
                    expr(RawExpr::Monop(
                        Monop::Neg,
                        expr(RawExpr::Finop(
                            Finop::Plus,
                            vec![variable_expr("y"), variable_expr("z")],
                        )),
                    )),
                ],
            )),
        ));
    }

    fn variable_expr(name: &str) -> Rc<MetaExpr<()>> {
        expr(RawExpr::Variable(variable(name)))
    }

    fn variable(name: &str) -> Variable {
        Variable {
            name: name.to_owned(),
            non_numeric_subscript: String::new(),
            annotations: Vec::new(),
        }
    }
}
