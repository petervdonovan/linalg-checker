use super::*;
use crate::{
    Annotation, Binop, Monop, SeqOp, Triop, from_tex,
    visit_mut::{Existence, VisitContext},
};
use expect_test::expect_file;
use z3::{SatResult, SortKind, ast::Bool};

fn expression(tex: &str) -> Expr<()> {
    from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap()
}
fn literal(n: u64) -> Expr<()> {
    Expr::new(RawExpr::NatLiteral(n))
}
fn variable(name: &str) -> Expr<()> {
    Expr::new(RawExpr::Variable(Variable::new(name)))
}
fn model_roundtrip<M>(codec: &mut ExprDatatype, input: &Expr<M>) -> Expr<()> {
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    let term = codec.constant("term");
    codec.assert_equal(&solver, &term, input).unwrap();
    assert_eq!(solver.check(), SatResult::Sat);
    let value = solver.get_model().unwrap().eval(&term, true).unwrap();
    let decoded = codec.decode(&value).unwrap();
    assert_eq!(
        codec.encode(&decoded).unwrap(),
        codec.encode(input).unwrap()
    );
    decoded
}

#[test]
fn arithmetic_query_snapshot_and_model_roundtrip() {
    let mut codec = ExprDatatype::new("arith");
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    let source = expression("1+2+3");
    let term = codec.constant("term");
    codec.assert_equal(&solver, &term, &source).unwrap();
    expect_file!["snapshots/arithmetic.smt2"].assert_eq(&solver.to_smt2());
    assert_eq!(solver.check(), SatResult::Sat);
    let value = solver.get_model().unwrap().eval(&term, true).unwrap();
    let result = codec.decode(&value).unwrap();
    assert_eq!(
        result,
        Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![literal(1), literal(2), literal(3)]
        ))
    );
    assert_eq!(
        codec.encode(&result).unwrap(),
        codec.encode(&source).unwrap()
    );
}

#[test]
fn quantified_query_snapshot_and_model_roundtrip() {
    let mut codec = ExprDatatype::new("quant");
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    let source = expression(r"\forall x \in \mathbb{R}, y \in \mathbb{R}, x+y=y+x");
    let term = codec.constant("formula");
    codec.assert_equal(&solver, &term, &source).unwrap();
    let query = solver.to_smt2();
    expect_file!["snapshots/quantified.smt2"].assert_eq(&query);
    assert!(!query.contains("(forall"));
    assert!(!query.contains("(exists"));
    assert_eq!(solver.check(), SatResult::Sat);
    let value = solver.get_model().unwrap().eval(&term, true).unwrap();
    assert_eq!(codec.decode(&value).unwrap(), source);
}

#[test]
fn datatype_fields_use_only_datatypes_and_core_booleans() {
    let codec = ExprDatatype::new("fields");
    let s = &codec.schema;
    for sort in [
        &s.natural,
        &s.positive,
        &s.monop.sort,
        &s.binop.sort,
        &s.finop.sort,
        &s.quantifier.sort,
        &s.comparison.sort,
        &s.seqop.sort,
        &s.expr,
        &s.ty,
        &s.list,
    ] {
        assert_eq!(sort.sort.kind(), SortKind::Datatype);
        for variant in &sort.variants {
            for i in 0..variant.constructor.arity() {
                assert!(matches!(
                    variant.constructor.domain(i),
                    Some(SortKind::Datatype | SortKind::Bool)
                ));
            }
        }
    }
    assert!(!s.monop.values.iter().any(|(op, _)| *op == Monop::Norm2));
}

#[test]
fn all_supported_operator_families_roundtrip_through_models() {
    let mut codec = ExprDatatype::new("operators");
    for &(op, _) in schema::MONOPS {
        let operand = match op {
            Monop::Not => Expr::new(RawExpr::BoolLiteral(true)),
            Monop::Diag => variable("s"),
            Monop::Neg => variable("x"),
            _ => variable("A"),
        };
        let input = Expr::new(RawExpr::Monop(op, operand));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    for &(op, _) in schema::BINOPS {
        let (left, right) = match op {
            Binop::Cast => (Expr::new(RawExpr::Type(TypeExpr::Real)), variable("A")),
            Binop::ElementOf | Binop::InDomain => {
                (variable("x"), Expr::new(RawExpr::Type(TypeExpr::Real)))
            }
            Binop::SingleSubscript => (variable("s"), literal(1)),
            _ => (variable("x"), literal(2)),
        };
        let input = Expr::new(RawExpr::Binop(op, left, right));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    for &(op, _) in schema::FINOPS {
        let values = if matches!(op, Finop::And | Finop::Or) {
            vec![
                Expr::new(RawExpr::BoolLiteral(true)),
                Expr::new(RawExpr::BoolLiteral(false)),
                variable("P"),
            ]
        } else {
            vec![literal(1), literal(2), literal(3)]
        };
        let input = Expr::new(RawExpr::Finop(op, values));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    for &(op, _) in schema::COMPARISONS {
        let input = Expr::new(RawExpr::CmpChain(CmpChain {
            start: literal(1),
            assertions: vec![(op, literal(2))],
        }));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    for &(op, _) in schema::SEQOPS {
        let body = if op == SeqOp::BigOr {
            expression("i>0")
        } else {
            variable("i")
        };
        let input = Expr::new(RawExpr::Seqop(
            op,
            Range {
                index_variable: Variable::new("i"),
                from: literal(1),
                to: literal(3),
            },
            body,
        ));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    for tex in [
        r"P \implies Q",
        r"\exists x \in \mathbb{R}, x>0",
        r"\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x=y\right)",
        r"\left\{x \in \mathbb{R} : x>0\right\}",
        r"\emptyset",
    ] {
        let input = expression(tex);
        assert_eq!(model_roundtrip(&mut codec, &input), input, "{tex}");
    }
}

#[test]
fn comparison_chains_keep_adjacent_pair_semantics() {
    let mut codec = ExprDatatype::new("chain");
    let result = model_roundtrip(&mut codec, &expression("1<2<3<4"));
    assert_eq!(
        result,
        Expr::new(RawExpr::Finop(
            Finop::And,
            vec![expression("1<2"), expression("2<3"), expression("3<4")]
        ))
    );
}

#[test]
fn finop_argument_lists_preserve_arity_and_explicit_nesting() {
    let mut codec = ExprDatatype::new("finop_lists");
    for &(op, _) in schema::FINOPS {
        for values in [
            vec![],
            vec![variable("only")],
            vec![variable("a"), variable("b"), variable("c")],
            vec![
                variable("a"),
                Expr::new(RawExpr::Finop(op, vec![variable("b"), variable("c")])),
            ],
        ] {
            let input = Expr::new(RawExpr::Finop(op, values));
            assert_eq!(model_roundtrip(&mut codec, &input), input);
        }
    }
}

#[test]
fn matrices_sequences_and_quantifier_premise_groups_keep_their_structure() {
    let mut codec = ExprDatatype::new("collections");
    for tex in [
        r"\begin{bmatrix}1 & x \\ 3 & 4\end{bmatrix}",
        r"\begin{bmatrix}\end{bmatrix}",
        r"\begin{bmatrix}\begin{bmatrix}1 & 2\end{bmatrix} & 3\end{bmatrix}",
        "(1, 2, 3)",
        "((1, 2), (3, 4))",
        r"\forall x \in \mathbb{R}, x>0, x=x",
    ] {
        let input = expression(tex);
        assert_eq!(model_roundtrip(&mut codec, &input), input, "{tex}");
    }
}

#[test]
fn types_and_bound_natural_positions_are_structural_data() {
    let mut codec = ExprDatatype::new("types");
    let bound = Expr::new(RawExpr::BoundNatural(DeBruijnIndex::new(0)));
    let dependent = TypeExpr::Seq(
        Expr::new(RawExpr::Type(TypeExpr::Matrix(bound, literal(1)))),
        literal(3),
    );
    for ty in [
        TypeExpr::Bool,
        TypeExpr::Nat,
        TypeExpr::Int,
        TypeExpr::Real,
        TypeExpr::Set(Box::new(TypeExpr::Real)),
        TypeExpr::Matrix(variable("n"), literal(2)),
        dependent,
    ] {
        let input = Expr::new(RawExpr::Type(ty));
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    let input = Expr::new(RawExpr::Type(TypeExpr::Seq(
        Expr::new(RawExpr::Type(TypeExpr::Seq(
            Expr::new(RawExpr::Type(TypeExpr::Real)),
            literal(2),
        ))),
        literal(3),
    )));
    assert_eq!(model_roundtrip(&mut codec, &input), input);
}

#[test]
fn interning_preserves_full_variable_identity_and_ignores_metadata() {
    let mut codec = ExprDatatype::new("names");
    let input = expression(r"\hat{x}_{\text{i}}^{\prime}");
    assert_eq!(model_roundtrip(&mut codec, &input), input);
    let first = Variable {
        name: "x".into(),
        non_numeric_subscript: "basis".into(),
        annotations: vec![Annotation::Prime, Annotation::Hat],
    };
    let mut second = first.clone();
    second.annotations.reverse();
    assert_eq!(first.z3_name(), second.z3_name());
    let first = Expr::with_metadata("ignored", RawExpr::Variable(first));
    let second: Expr<()> = Expr::new(RawExpr::Variable(second));
    assert_eq!(
        model_roundtrip(&mut codec, &first),
        first.with_default_metadata::<()>()
    );
    assert_ne!(
        codec.encode(&first).unwrap(),
        codec.encode(&second).unwrap()
    );
}

#[test]
fn implicit_dimension_ids_preserve_sharing_and_are_local_to_the_codec() {
    let mut codec = ExprDatatype::new("dimensions");
    let a = ImplicitDimension::fresh();
    let b = ImplicitDimension::fresh();
    let input = Expr::new(RawExpr::Finop(
        Finop::SeqLiteral,
        vec![
            Expr::new(RawExpr::IdentityMatrix { dimension: a }),
            Expr::new(RawExpr::ZeroMatrix { rows: a, cols: b }),
            Expr::new(RawExpr::StandardBasis {
                index: literal(1),
                dimension: b,
            }),
            Expr::new(RawExpr::ImplicitDimension(a)),
        ],
    ));
    assert_eq!(model_roundtrip(&mut codec, &input), input);
    assert_eq!(codec.dimensions.values, vec![a, b]);
    let mut other = ExprDatatype::new("other_dimensions");
    let fresh: Expr<()> = Expr::new(RawExpr::IdentityMatrix {
        dimension: ImplicitDimension::fresh(),
    });
    let result = other.encode(&fresh).unwrap();
    assert_eq!(
        tag(&field(&result, 0).unwrap(), &other.schema.natural).unwrap(),
        "NZero"
    );
}

#[test]
fn compact_naturals_cover_the_full_u64_range() {
    let mut codec = ExprDatatype::new("numbers");
    for n in [0, 1, 2, 3, 4, 255, 256, u64::MAX] {
        let input = literal(n);
        assert_eq!(model_roundtrip(&mut codec, &input), input);
    }
    let mut value = codec.encode(&literal(u64::MAX)).unwrap();
    let mut nodes = 1;
    while let Some(child) = value.nth_child(0) {
        value = child.as_datatype().unwrap();
        nodes += 1;
    }
    assert_eq!(nodes, 66); // Expr wrapper, Natural wrapper, and 64 binary digits.
}

#[test]
fn unsupported_forms_and_invalid_arities_do_not_add_assertions() {
    let mut codec = ExprDatatype::new("unsupported");
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    let term = codec.constant("term");
    let mut inputs = vec![
        Expr::new(RawExpr::Hole),
        Expr::new(RawExpr::Ellipsis),
        expression(r"P \iff Q"),
        expression(r"P \implies Q \implies R"),
        Expr::new(RawExpr::Triop(
            Triop::DoubleSubscript,
            variable("A"),
            literal(1),
            literal(2),
        )),
    ];
    for op in [
        Monop::Norm2,
        Monop::Nul,
        Monop::Range,
        Monop::SetLiteral,
        Monop::Inverse,
        Monop::Norm1,
        Monop::NormInfty,
        Monop::NormFrob,
    ] {
        inputs.push(Expr::new(RawExpr::Monop(op, variable("x"))));
    }
    for op in [
        Binop::InnerProd,
        Binop::SetIntersection,
        Binop::SetUnion,
        Binop::SetDifference,
    ] {
        inputs.push(Expr::new(RawExpr::Binop(op, variable("x"), variable("y"))));
    }
    for op in [Finop::Max, Finop::Min] {
        inputs.push(Expr::new(RawExpr::Finop(op, vec![literal(1), literal(2)])));
    }
    for input in inputs {
        assert!(matches!(
            codec.assert_equal(&solver, &term, &input),
            Err(Error::Unsupported(_))
        ));
        assert!(solver.get_assertions().is_empty());
    }
    for input in [
        Expr::new(RawExpr::Finop(Finop::Forall, vec![literal(1)])),
        Expr::new(RawExpr::Finop(Finop::SeqLiteral, vec![])),
        Expr::new(RawExpr::CmpChain(CmpChain {
            start: literal(1),
            assertions: vec![],
        })),
    ] {
        assert!(matches!(
            codec.assert_equal(&solver, &term, &input),
            Err(Error::Malformed(_))
        ));
        assert!(solver.get_assertions().is_empty());
    }
}

#[test]
fn decoding_rejects_foreign_sorts_unknown_ids_and_unevaluated_values() {
    let mut codec = ExprDatatype::new("decode_errors");
    let mut foreign = ExprDatatype::new("foreign");
    let foreign = foreign.encode(&literal(0)).unwrap();
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    assert_eq!(
        codec.assert_equal(&solver, &foreign, &literal(0)),
        Err(Error::WrongSort)
    );
    assert!(solver.get_assertions().is_empty());
    assert_eq!(codec.decode(&foreign), Err(Error::WrongSort));
    assert_eq!(
        codec.decode(&codec.constant("unevaluated")),
        Err(Error::UnevaluatedTerm)
    );
    let unknown = codec.node("Var", &[codec.schema.natural(17)]);
    assert_eq!(
        codec.decode(&unknown),
        Err(Error::UnknownAtom {
            kind: "variable",
            id: 17
        })
    );
    let unknown = codec.node("Identity", &[codec.schema.natural(2)]);
    assert_eq!(
        codec.decode(&unknown),
        Err(Error::UnknownAtom {
            kind: "implicit dimension",
            id: 2
        })
    );
    let bool_ctor = codec
        .schema
        .expr
        .variants
        .iter()
        .find(|v| v.constructor.name().ends_with(".BoolLiteral"))
        .unwrap();
    let unknown_bool = bool_ctor
        .constructor
        .apply(&[&Bool::new_const("b")])
        .as_datatype()
        .unwrap();
    assert_eq!(codec.decode(&unknown_bool), Err(Error::UnevaluatedTerm));
}

#[test]
fn decoding_rejects_overflow_and_malformed_model_structures() {
    let codec = ExprDatatype::new("malformed");
    let mut positive = app(&codec.schema.positive, "POne", &[]);
    for _ in 0..64 {
        positive = app(&codec.schema.positive, "PDouble", &[positive]);
    }
    let natural = app(&codec.schema.natural, "NPositive", &[positive]);
    assert_eq!(
        codec.decode(&codec.node("NatLiteral", &[natural])),
        Err(Error::NumericOverflow)
    );
    let nil = app(&codec.schema.list, "ExprNil", &[]);
    let matrix = codec.node(
        "MatrixLiteral",
        &[
            codec.schema.natural(2),
            codec.schema.natural(2),
            nil.clone(),
        ],
    );
    assert!(matches!(codec.decode(&matrix), Err(Error::Malformed(_))));
    let quantifier = codec.node(
        "Quantified",
        &[
            codec.schema.quantifier.encode(Finop::Forall).unwrap(),
            nil.clone(),
            codec.node("NatLiteral", &[codec.schema.natural(1)]),
        ],
    );
    assert!(matches!(
        codec.decode(&quantifier),
        Err(Error::Malformed(_))
    ));
    assert!(matches!(
        codec.decode(&codec.node("SequenceLiteral", &[nil])),
        Err(Error::Malformed(_))
    ));
}

#[test]
fn core_encoding_uses_existing_norm_rewriting_including_generated_conditions() {
    let input = expression(r"\left\lVert v \right\rVert_{2}");
    let mut codec = ExprDatatype::new("norm");
    assert!(matches!(codec.encode(&input), Err(Error::Unsupported(_))));
    let types = crate::enumerable_envspec::infer_symbolic_type_environment(&[expression(
        r"v \in \mathbb{R}^{2}",
    )])
    .unwrap();
    let prepared =
        crate::preprocessing::prepare_expression(&types, &input, VisitContext::positive()).unwrap();
    assert!(!prepared.side_conditions.is_empty());
    model_roundtrip(&mut codec, &prepared.expression);
    for condition in &prepared.side_conditions {
        for assertion in &condition.defining_assertions {
            model_roundtrip(&mut codec, assertion);
        }
        if let Existence::Checkable(assertions) = &condition.existence {
            for assertion in assertions {
                model_roundtrip(&mut codec, assertion);
            }
        }
    }
}

#[test]
fn syntax_encoding_does_not_evaluate_arithmetic() {
    let mut codec = ExprDatatype::new("syntax");
    let sum = codec.encode(&expression("1+2")).unwrap();
    let three = codec.encode(&literal(3)).unwrap();
    let solver = Solver::new_for_logic("QF_DT").unwrap();
    solver.assert(sum.eq(&three));
    assert_eq!(solver.check(), SatResult::Unsat);
}
