use std::fmt;

use crate::{
    Binop, Cmp, CmpChain, Expr, Finop, Logic, LogicChain, Matrix, Monop, SeqOp, Triop, TypeExpr,
    Variable,
};

impl<Metadata> fmt::Display for AsLatex<Metadata> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        expr_with_mode(f, &self.e, self.verbose)
    }
}

pub struct AsLatex<Metadata> {
    e: Expr<Metadata>,
    verbose: bool,
}

impl<Metadata> Expr<Metadata> {
    pub fn as_latex(&self) -> AsLatex<Metadata> {
        AsLatex {
            e: self.clone(),
            verbose: false,
        }
    }

    pub fn as_latex_verbose(&self) -> AsLatex<Metadata> {
        AsLatex {
            e: self.clone(),
            verbose: true,
        }
    }
}

pub fn expr<Metadata>(f: &mut fmt::Formatter<'_>, e: &Expr<Metadata>) -> fmt::Result {
    expr_with_mode(f, e, false)
}

fn expr_with_mode<Metadata>(
    f: &mut fmt::Formatter<'_>,
    e: &Expr<Metadata>,
    verbose: bool,
) -> fmt::Result {
    match &e.raw {
        crate::RawExpr::SetComprehension {
            variable: binder,
            domain,
            predicate,
        } => {
            write!(f, r"\left\{{")?;
            variable(f, binder)?;
            write!(f, r" \in ")?;
            type_expr(f, domain, verbose)?;
            write!(f, " : ")?;
            expr_with_mode(f, predicate, verbose)?;
            write!(f, r"\right\}}")
        }
        crate::RawExpr::Hole => write!(f, r"\square"),
        crate::RawExpr::Ellipsis => write!(f, r"\ldots"),
        crate::RawExpr::ImplicitDimension(dimension) if verbose => {
            write!(f, "@{}", dimension.nonce_id())
        }
        crate::RawExpr::ImplicitDimension(_) => {
            panic!("implicit dimension leaves cannot be rendered in ordinary TeX")
        }
        crate::RawExpr::BoundNatural(index) if verbose => {
            write!(f, r"\#{}", index.get())
        }
        crate::RawExpr::BoundNatural(_) => {
            panic!("bound natural indices are internal and cannot be rendered")
        }
        crate::RawExpr::IdentityMatrix { dimension } if verbose => {
            write!(f, "I_{{@{}}}", dimension.nonce_id())
        }
        crate::RawExpr::IdentityMatrix { .. } => write!(f, "I"),
        crate::RawExpr::StandardBasis { index, dimension } => {
            write!(f, "e_{{")?;
            expr_with_mode(f, index, verbose)?;
            if verbose {
                write!(f, ",@{}", dimension.nonce_id())?;
            }
            write!(f, "}}")
        }
        crate::RawExpr::ZeroMatrix { rows, cols } if verbose => write!(
            f,
            r"\mathbb{{0}}_{{@{},@{}}}",
            rows.nonce_id(),
            cols.nonce_id()
        ),
        crate::RawExpr::ZeroMatrix { .. } => write!(f, r"\mathbb{{0}}"),
        crate::RawExpr::Type(ty) => type_expr(f, ty, verbose),
        crate::RawExpr::Variable(v) => variable(f, v),
        crate::RawExpr::NatLiteral(value) => write!(f, "{value}"),
        crate::RawExpr::Matrix(value) => matrix(f, value, verbose),
        crate::RawExpr::Monop(op, e) => monop(f, op, |f| {
            let grouped = match op {
                Monop::Neg => precedence(e) <= Precedence::Addition,
                Monop::Inverse | Monop::Transpose => precedence(e) < Precedence::Power,
                _ => false,
            };
            grouped_expr(f, e, grouped, verbose)
        }),
        crate::RawExpr::Binop(op, e0, e1) => binop(
            f,
            op,
            |f| {
                grouped_expr(
                    f,
                    e0,
                    (matches!(op, Binop::Power) && precedence(e0) < Precedence::Power)
                        || (matches!(op, Binop::ElementOf | Binop::InDomain)
                            && precedence(e0) <= Precedence::Comparison),
                    verbose,
                )
            },
            |f| {
                grouped_expr(
                    f,
                    e1,
                    matches!(op, Binop::ElementOf | Binop::InDomain) && precedence(e1) <= Precedence::Comparison,
                    verbose,
                )
            },
        ),
        crate::RawExpr::Triop(op, e0, e1, e2) => triop(
            f,
            op,
            |f| expr_with_mode(f, e0, verbose),
            |f| expr_with_mode(f, e1, verbose),
            |f| expr_with_mode(f, e2, verbose),
        ),
        crate::RawExpr::Finop(op, exprs) => finop(f, op, exprs.iter(), verbose),
        crate::RawExpr::CmpChain(chain) => cmp_chain(f, chain, verbose),
        crate::RawExpr::LogicChain(chain) => logic_chain(f, chain, verbose),
        crate::RawExpr::Seqop(op, range, body) => seqop(
            f,
            op,
            &range.index_variable.name,
            |f| expr_with_mode(f, &range.from, verbose),
            |f| expr_with_mode(f, &range.to, verbose),
            |f| grouped_expr(f, body, precedence(body) <= Precedence::Addition, verbose),
        ),
    }
}

fn matrix<Metadata>(
    f: &mut fmt::Formatter<'_>,
    matrix: &Matrix<Expr<Metadata>>,
    verbose: bool,
) -> fmt::Result {
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
            expr_with_mode(f, &matrix.at(row, column), verbose)?;
        }
    }
    write!(f, r"\end{{bmatrix}}")
}

fn grouped_expr<Metadata>(
    f: &mut fmt::Formatter<'_>,
    e: &Expr<Metadata>,
    grouped: bool,
    verbose: bool,
) -> fmt::Result {
    if grouped {
        write!(f, r"\left(")?;
    }
    expr_with_mode(f, e, verbose)?;
    if grouped {
        write!(f, r"\right)")?;
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Forall,
    Logic,
    Or,
    And,
    Comparison,
    Sequence,
    Addition,
    Multiplication,
    Prefix,
    Power,
    Atom,
}

fn precedence<Metadata>(e: &Expr<Metadata>) -> Precedence {
    match &e.raw {
        crate::RawExpr::Finop(Finop::Forall | Finop::Exists, _) => Precedence::Forall,
        crate::RawExpr::LogicChain(_) => Precedence::Logic,
        crate::RawExpr::Finop(Finop::Or, _) => Precedence::Or,
        crate::RawExpr::Finop(Finop::And, _) => Precedence::And,
        crate::RawExpr::CmpChain(_) | crate::RawExpr::Binop(Binop::ElementOf | Binop::InDomain, _, _) => {
            Precedence::Comparison
        }
        crate::RawExpr::Finop(Finop::SeqLiteral, _) => Precedence::Sequence,
        crate::RawExpr::Finop(Finop::Plus, _) => Precedence::Addition,
        crate::RawExpr::Finop(Finop::Times, _) | crate::RawExpr::Binop(Binop::Div, _, _) => {
            Precedence::Multiplication
        }
        crate::RawExpr::Monop(Monop::Neg | Monop::Diag, _) => Precedence::Prefix,
        crate::RawExpr::Monop(Monop::Inverse | Monop::Transpose, _)
        | crate::RawExpr::Binop(Binop::Power, _, _) => Precedence::Power,
        _ => Precedence::Atom,
    }
}

fn type_expr<Metadata>(
    f: &mut fmt::Formatter<'_>,
    ty: &TypeExpr<Metadata>,
    verbose: bool,
) -> fmt::Result {
    match ty {
        TypeExpr::Set(element) => {
            write!(f, r"\operatorname{{Set}}(")?;
            type_expr(f, element, verbose)?;
            write!(f, ")")
        }
        TypeExpr::Bool => write!(f, r"\mathbb{{B}}"),
        TypeExpr::Nat => write!(f, r"\mathbb{{N}}"),
        TypeExpr::Int => write!(f, r"\mathbb{{Z}}"),
        TypeExpr::Real => write!(f, r"\mathbb{{R}}"),
        TypeExpr::Matrix(rows, cols) if matches!(cols.raw, crate::RawExpr::NatLiteral(1)) => {
            write!(f, r"\mathbb{{R}}^{{")?;
            expr_with_mode(f, rows, verbose)?;
            write!(f, "}}")
        }
        TypeExpr::Matrix(rows, cols) => {
            write!(f, r"\mathbb{{R}}^{{")?;
            expr_with_mode(f, rows, verbose)?;
            write!(f, r" \times ")?;
            expr_with_mode(f, cols, verbose)?;
            write!(f, "}}")
        }
        TypeExpr::Seq(element, size) => {
            write!(f, r"\operatorname{{Seq}}_{{")?;
            expr_with_mode(f, size, verbose)?;
            write!(f, "}}(")?;
            expr_with_mode(f, element, verbose)?;
            write!(f, ")")
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
        write!(f, "_{{\\text{{{}}}}}", v.non_numeric_subscript)?;
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
        Monop::Det => write!(f, r"\det(")?,
        Monop::Diag => write!(f, r"\operatorname{{diag}}(")?,
        Monop::Nul => write!(f, r"\operatorname{{Nul}}(")?,
        Monop::Neg => write!(f, "-")?,
        Monop::Inverse => {}
        Monop::Transpose => {}
        Monop::Norm1 | Monop::Norm2 | Monop::NormInfty | Monop::NormFrob => {
            write!(f, r"\left\lVert ")?
        }
    }

    e(f)?;

    match op {
        Monop::Trace | Monop::Det | Monop::Diag | Monop::Nul => write!(f, ")"),
        Monop::Neg => Ok(()),
        Monop::Inverse => write!(f, "^{{-1}}"),
        Monop::Transpose => write!(f, r"^\top"),
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
        Binop::Cast => {
            write!(f, r"\operatorname{{cast}}(")?;
            e0(f)?;
            write!(f, ", ")?;
            e1(f)?;
            write!(f, ")")
        }
        Binop::ElementOf | Binop::InDomain => {
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

fn finop<'a, Metadata: 'a, I>(
    f: &mut fmt::Formatter<'_>,
    op: &Finop,
    exprs: I,
    verbose: bool,
) -> fmt::Result
where
    I: IntoIterator<Item = &'a Expr<Metadata>>,
{
    let exprs = exprs.into_iter().collect::<Vec<_>>();
    if matches!(op, Finop::SeqLiteral) {
        assert!(
            exprs.len() >= 2,
            "sequence literals require at least two expressions"
        );
    }
    if matches!(op, Finop::Forall | Finop::Exists) {
        write!(
            f,
            "{}",
            match op {
                Finop::Forall => r"\forall ",
                Finop::Exists => r"\exists ",
                _ => unreachable!(),
            }
        )?;
        for (index, expression) in exprs.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            grouped_expr(f, expression, is_quantifier_expression(expression), verbose)?;
        }
        return Ok(());
    }
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
            grouped_expr(f, inner, precedence(inner) <= Precedence::Addition, verbose)?;
            continue;
        }

        if index > 0 {
            write!(f, "{}", finop_separator(op))?;
        }
        let grouped = match op {
            Finop::Plus => precedence(expression) < Precedence::Addition,
            Finop::Times => {
                precedence(expression) < Precedence::Multiplication
                    || matches!(&expression.raw, crate::RawExpr::Monop(Monop::Neg, _))
            }
            Finop::And => precedence(expression) < Precedence::And,
            Finop::Or => precedence(expression) < Precedence::Or,
            Finop::SeqLiteral => precedence(expression) <= Precedence::Sequence,
            Finop::Forall | Finop::Exists => unreachable!(),
            _ => false,
        };
        grouped_expr(f, expression, grouped, verbose)?;
    }

    match op {
        Finop::Max | Finop::Min => write!(f, ")"),
        Finop::Forall | Finop::Exists => unreachable!(),
        _ => Ok(()),
    }
}

fn is_quantifier_expression<Metadata>(expression: &Expr<Metadata>) -> bool {
    matches!(
        expression.raw,
        crate::RawExpr::Finop(Finop::Forall | Finop::Exists, _)
    )
}

fn cmp_chain<Metadata>(
    f: &mut fmt::Formatter<'_>,
    chain: &CmpChain<Metadata>,
    verbose: bool,
) -> fmt::Result {
    grouped_expr(
        f,
        &chain.start,
        precedence(&chain.start) <= Precedence::Comparison,
        verbose,
    )?;
    for (op, expression) in &chain.assertions {
        write!(f, " {} ", cmp_symbol(op))?;
        grouped_expr(
            f,
            expression,
            precedence(expression) <= Precedence::Comparison,
            verbose,
        )?;
    }
    Ok(())
}

fn logic_chain<Metadata>(
    f: &mut fmt::Formatter<'_>,
    chain: &LogicChain<Metadata>,
    verbose: bool,
) -> fmt::Result {
    grouped_expr(
        f,
        &chain.start,
        precedence(&chain.start) <= Precedence::Logic,
        verbose,
    )?;
    for (op, expression) in &chain.assertions {
        write!(f, " {} ", logic_symbol(op))?;
        grouped_expr(
            f,
            expression,
            precedence(expression) <= Precedence::Logic,
            verbose,
        )?;
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
        SeqOp::Map => write!(f, r"\operatorname{{map}}")?,
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
        Finop::And => r" \land ",
        Finop::Or => r" \lor ",
        Finop::Forall | Finop::Exists => ", ",
        Finop::Max | Finop::Min => ", ",
        Finop::SeqLiteral => ", ",
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::{
        Annotation, Binop, Cmp, CmpChain, Expr, Finop, ImplicitDimension, Logic, LogicChain,
        Matrix, Monop, Range, RawExpr, SeqOp, Triop, TypeExpr, Variable,
    };

    fn as_latex(raw: RawExpr<()>) -> String {
        Expr::new(raw).as_latex().to_string()
    }

    fn matrix_type(rows: u64, cols: u64) -> TypeExpr<()> {
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows)),
            Expr::new(RawExpr::NatLiteral(cols)),
        )
    }

    #[test]
    fn verbose_latex_exposes_implicit_dimension_nonces_only_internally() {
        let identity = ImplicitDimension::fresh();
        let rows = ImplicitDimension::fresh();
        let cols = ImplicitDimension::fresh();
        let expression: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::IdentityMatrix {
                    dimension: identity,
                }),
                Expr::new(RawExpr::ZeroMatrix { rows, cols }),
            ],
        ));
        assert_eq!(expression.as_latex().to_string(), r"I + \mathbb{0}");
        assert_eq!(
            expression.as_latex_verbose().to_string(),
            format!(
                r"I_{{@{}}} + \mathbb{{0}}_{{@{},@{}}}",
                identity.nonce_id(),
                rows.nonce_id(),
                cols.nonce_id()
            )
        );

        let bound = Expr::<()>::new(RawExpr::BoundNatural(crate::DeBruijnIndex::new(0)));
        assert_eq!(bound.as_latex_verbose().to_string(), r"\#0");
        assert_eq!(
            Expr::<()>::new(RawExpr::NatLiteral(0))
                .as_latex()
                .to_string(),
            "0"
        );
    }

    #[test]
    #[should_panic(expected = "bound natural indices are internal")]
    fn ordinary_latex_rejects_bound_natural_indices() {
        Expr::<()>::new(RawExpr::BoundNatural(crate::DeBruijnIndex::new(0)))
            .as_latex()
            .to_string();
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
    fn test_ellipsis() {
        expect![r"\ldots"].assert_eq(&as_latex(RawExpr::Ellipsis));
    }

    #[test]
    fn test_types_and_membership() {
        let rendered_types = [
            TypeExpr::Bool,
            TypeExpr::Nat,
            TypeExpr::Int,
            TypeExpr::Real,
            matrix_type(3, 1),
            matrix_type(3, 4),
            matrix_type(1, 1),
        ]
        .map(|ty| as_latex(RawExpr::Type(ty)))
        .join("\n");
        expect![
            "\\mathbb{B}\n\\mathbb{N}\n\\mathbb{Z}\n\\mathbb{R}\n\\mathbb{R}^{3}\n\\mathbb{R}^{3 \\times 4}\n\\mathbb{R}^{1}"
        ]
        .assert_eq(&rendered_types);

        expect!["A \\in \\mathbb{R}^{2 \\times 3}"].assert_eq(&as_latex(RawExpr::Binop(
            Binop::ElementOf,
            variable_expr("A"),
            Expr::new(RawExpr::Type(matrix_type(2, 3))),
        )));
    }

    #[test]
    fn test_cast() {
        expect![r"\operatorname{cast}(\mathbb{R}, x + y)"].assert_eq(&as_latex(RawExpr::Binop(
            Binop::Cast,
            Expr::new(RawExpr::Type(TypeExpr::Real)),
            Expr::new(RawExpr::Finop(
                Finop::Plus,
                vec![variable_expr("x"), variable_expr("y")],
            )),
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
        expect!["\\hat{x}_{\\text{i}}^{\\prime}"].assert_eq(&as_latex(RawExpr::Variable(
            Variable {
                name: "x".to_owned(),
                non_numeric_subscript: "i".to_owned(),
                annotations: vec![Annotation::Hat, Annotation::Prime],
            },
        )));
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
        expect!["\\operatorname{tr}(x)\n\\det(x)\n\\operatorname{diag}(x)\n\\operatorname{Nul}(x)\n-x\nx^{-1}"].assert_eq(
            &format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                as_latex(RawExpr::Monop(
                    Monop::Trace,
                    Expr::new(RawExpr::Variable(Variable::new("x"))),
                )),
                as_latex(RawExpr::Monop(
                    Monop::Det,
                    Expr::new(RawExpr::Variable(Variable::new("x"))),
                )),
                as_latex(RawExpr::Monop(
                    Monop::Diag,
                    Expr::new(RawExpr::Variable(Variable::new("x"))),
                )),
                as_latex(RawExpr::Monop(
                    Monop::Nul,
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
            ),
        );
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

        expect!["1 + 2\nx y\n\\max(1, 2)\n\\min(1, 2)\n1, 2"].assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}",
            as_latex(RawExpr::Finop(Finop::Plus, values.clone())),
            as_latex(RawExpr::Finop(Finop::Times, factors)),
            as_latex(RawExpr::Finop(Finop::Max, values.clone())),
            as_latex(RawExpr::Finop(Finop::Min, values.clone())),
            as_latex(RawExpr::Finop(Finop::SeqLiteral, values)),
        ));
    }

    #[test]
    fn test_sequence_operators() {
        let sequence = |op| {
            RawExpr::Seqop(
                op,
                Range {
                    index_variable: Variable::new("i"),
                    from: Expr::new(RawExpr::NatLiteral(1)),
                    to: Expr::new(RawExpr::NatLiteral(3)),
                },
                Expr::new(RawExpr::Variable(Variable::new("i"))),
            )
        };

        expect!["\\sum_{i=1}^{3}i\n\\prod_{i=1}^{3}i\n\\operatorname{map}_{i=1}^{3}i"].assert_eq(
            &format!(
                "{}\n{}\n{}",
                as_latex(sequence(SeqOp::Sum)),
                as_latex(sequence(SeqOp::Prod)),
                as_latex(sequence(SeqOp::Map)),
            ),
        );
    }

    #[test]
    fn test_sequence_body_grouping() {
        let sequence = |body| {
            RawExpr::Seqop(
                SeqOp::Sum,
                Range {
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
            "\\left(x + y\\right) z\n\\left(x + y\\right)^{2}\n-\\left(x + y\\right)\n\\left(x + y\\right)^{-1}\nx \\left(-y\\right)\n\\left(\\frac{1}{2}\\right)^{\\frac{1}{2}}"
        ]
        .assert_eq(&format!(
            "{}\n{}\n{}\n{}\n{}\n{}",
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
            as_latex(RawExpr::Binop(
                Binop::Power,
                Expr::new(RawExpr::Binop(
                    Binop::Div,
                    Expr::new(RawExpr::NatLiteral(1)),
                    Expr::new(RawExpr::NatLiteral(2)),
                )),
                Expr::new(RawExpr::Binop(
                    Binop::Div,
                    Expr::new(RawExpr::NatLiteral(1)),
                    Expr::new(RawExpr::NatLiteral(2)),
                )),
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
