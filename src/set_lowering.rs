//! Exact elimination of direct membership in typed set comprehensions.

use crate::{
    Binop, Expr, Finop, RawExpr,
    formula::substitute_free_variable,
    type_resolver::{MaybeTyped, TypeError, TypedMetadata},
    visit_mut::{self, VisitContext, VisitMut},
};

#[derive(Default)]
pub struct SetMembershipLowering {
    rewrites: usize,
    error: Option<TypeError>,
}

impl SetMembershipLowering {
    pub fn finish(self) -> Result<usize, TypeError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }
}

impl VisitMut<TypedMetadata> for SetMembershipLowering {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        if let RawExpr::Binop(Binop::ElementOf, subject, set) = &node.raw
            && let RawExpr::SetComprehension {
                variable,
                domain,
                predicate,
            } = &set.raw
        {
            if predicate.meta.get_type() != Ok(crate::TypeExpr::Bool) {
                self.error = Some(TypeError::Invalid(
                    "set comprehension predicate must be Boolean",
                ));
                return;
            }
            let subject = subject.with_default_metadata();
            let predicate =
                substitute_free_variable(&predicate.with_default_metadata(), variable, &subject);
            let alternatives = set
                .meta
                .alternatives()
                .iter()
                .map(|alternative| substitute_free_variable(alternative, variable, &subject))
                .collect::<Vec<_>>();
            let domain_check = Expr::new(RawExpr::Binop(
                Binop::InDomain,
                subject,
                Expr::new(RawExpr::Type(domain.with_default_metadata())),
            ));
            let replacement: Expr<()> =
                Expr::new(RawExpr::Finop(Finop::And, vec![domain_check, predicate]));
            // Substitution changes dependent types; infer them afresh next iteration.
            *node = replacement.with_default_metadata();
            let metadata = &mut node
                .get_mut()
                .expect("new membership replacement must be uniquely owned")
                .meta;
            for alternative in alternatives {
                metadata.add_alternative(alternative);
            }
            self.rewrites += 1;
            return;
        }
        // An unapplied comprehension is surface syntax. Do not lower operators
        // under its binder or introduce free synthetic definitions there.
        if matches!(node.raw, RawExpr::SetComprehension { .. }) {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        TypeExpr, Variable,
        enumerable_envspec::infer_symbolic_type_environment,
        formula::free_variables,
        preprocessing::{PreparedExpression, prepare_expression},
        type_resolver::{OperatorTypeRules, TypeResolver},
    };

    fn parse(tex: &str) -> Expr<()> {
        crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap()
    }
    fn prepare(tex: &str, givens: &[&str]) -> Result<PreparedExpression, TypeError> {
        let givens = givens.iter().map(|s| parse(s)).collect::<Vec<_>>();
        let types = infer_symbolic_type_environment(&givens).unwrap();
        prepare_expression(&types, &parse(tex), VisitContext::positive())
    }

    #[test]
    fn parses_and_renders_comprehensions_and_set_types() {
        let expected = r"\left\{x \in \mathbb{R} : x > 0\right\}";
        for input in [r"\{x \in \mathbb{R} : x > 0\}", expected] {
            assert_eq!(parse(input).as_latex().to_string(), expected);
        }
        for input in [
            r"\operatorname{Set}(\mathbb{R})",
            r"\operatorname{Set}(\mathbb{R}^{n \times n})",
        ] {
            let expression = parse(input);
            assert!(matches!(expression.raw, RawExpr::Type(TypeExpr::Set(_))));
            assert_eq!(expression.as_latex().to_string(), input);
        }
    }

    #[test]
    fn rejects_malformed_set_syntax() {
        for input in [
            r"\{x : x > 0\}",
            r"\{x + 1 \in \mathbb{R} : x > 0\}",
            r"\{x \in \mathbb{R} : \}",
            r"\{x \in S : x > 0\}",
        ] {
            assert!(
                crate::from_tex::expr(&ratex_parser::parse(input).unwrap()).is_err(),
                "{input}"
            );
        }
    }

    #[test]
    fn types_surface_comprehensions_without_exporting_the_binder() {
        let expression = parse(r"\{X \in \mathbb{R}^{n \times n} : X = A\}");
        let givens = [parse(r"A \in \mathbb{R}^{n \times n}")];
        let types = infer_symbolic_type_environment(&givens).unwrap();
        let mut typed = expression.with_default_metadata::<TypedMetadata>();
        TypeResolver::new(&types, &OperatorTypeRules::core())
            .resolve(&mut typed, VisitContext::positive())
            .unwrap();
        assert!(
            matches!(typed.meta.get_type().unwrap(), TypeExpr::Set(element) if matches!(*element, TypeExpr::Matrix(_, _)))
        );
        let free = free_variables(std::iter::once(&expression));
        assert!(free.contains(&Variable::new("A")));
        assert!(free.contains(&Variable::new("n")));
        assert!(!free.contains(&Variable::new("X")));
        let types = infer_symbolic_type_environment(&[parse(
            r"A \in \{X \in \mathbb{R}^{n \times n} : X = X\}",
        )])
        .unwrap();
        assert!(!types.types.contains_key(&Variable::new("X")));
        assert!(matches!(
            types.types[&Variable::new("A")],
            TypeExpr::Matrix(_, _)
        ));
    }

    #[test]
    fn lowers_compound_subject_and_nested_membership() {
        let prepared = prepare(
            r"y + 1 \in \{x \in \mathbb{R} : x > 0\}",
            &[r"y \in \mathbb{R}"],
        )
        .unwrap();
        assert_eq!(prepared.expression.meta.get_type(), Ok(TypeExpr::Bool));
        assert!(
            prepared
                .expression
                .as_latex()
                .to_string()
                .contains("y + 1 > 0")
        );
        let prepared = prepare(
            r"y \in \{x \in \mathbb{R} : x \in \{z \in \mathbb{R} : z > 0\}\}",
            &[r"y \in \mathbb{R}"],
        )
        .unwrap();
        assert!(
            !prepared
                .expression
                .as_latex()
                .to_string()
                .contains("left\\{")
        );
    }

    #[test]
    fn substitution_respects_shadowing_and_avoids_capture() {
        let expr = parse(r"\{y \in \mathbb{R} : x > y\}");
        let result = substitute_free_variable(&expr, &Variable::new("x"), &parse("y"));
        assert!(free_variables(std::iter::once(&result)).contains(&Variable::new("y")));
        let RawExpr::SetComprehension { variable, .. } = &result.raw else {
            panic!()
        };
        assert_ne!(variable, &Variable::new("y"));
        let expr = parse(r"\{x \in \mathbb{R} : x > 0\}");
        assert_eq!(
            substitute_free_variable(&expr, &Variable::new("x"), &parse("y")),
            expr
        );
        let prepared = prepare(
            r"j \in \{x \in \mathbb{R} : \sum_{j=1}^{2}x > 0\}",
            &[r"j \in \mathbb{R}"],
        )
        .unwrap();
        assert!(
            free_variables(std::iter::once(&prepared.expression)).contains(&Variable::new("j"))
        );
    }

    #[test]
    fn roots_and_norms_are_lowered_after_substitution() {
        let root = prepare(
            r"y \in \{x \in \mathbb{R} : x^{\frac{1}{2}} > 0\}",
            &[r"y \in \mathbb{R}"],
        )
        .unwrap();
        assert_eq!(root.side_conditions.len(), 1);
        for condition in &root.side_conditions {
            for definition in &condition.defining_assertions {
                assert!(!free_variables(std::iter::once(definition)).contains(&Variable::new("x")));
            }
        }
        let norm = prepare(
            r"v \in \{x \in \mathbb{R}^{n} : \left\lVert x\right\rVert_2 > 0\}",
            &[r"v \in \mathbb{R}^{n}"],
        )
        .unwrap();
        assert_eq!(norm.side_conditions.len(), 1);
    }

    #[test]
    fn nul_membership_lowers_through_a_generated_comprehension() {
        let prepared = prepare(
            r"z \in \operatorname{Nul}(A)",
            &[r"A \in \mathbb{R}^{m \times n}", r"z \in \mathbb{R}^{n}"],
        )
        .unwrap();
        let rendered = prepared.expression.as_latex().to_string();
        assert!(!rendered.contains("Nul"));
        assert!(!rendered.contains(r"\left\{"));
        assert!(rendered.contains(r"A z = \mathbb{0}"), "{rendered}");
        let set_value = prepare(
            r"\operatorname{Nul}(A)",
            &[r"A \in \mathbb{R}^{2 \times 2}"],
        )
        .unwrap();
        assert!(crate::to_z3::to_z3(&crate::Environment::default(), &set_value).is_err());
    }

    #[test]
    fn range_membership_lowers_through_a_positive_existential() {
        let prepared = prepare(
            r"b \in \operatorname{Range}(A)",
            &[r"A \in \mathbb{R}^{m \times n}", r"b \in \mathbb{R}^{m}"],
        )
        .unwrap();
        let rendered = prepared.expression.as_latex().to_string();
        assert!(!rendered.contains("Range"), "{rendered}");
        assert!(!rendered.contains(r"\left\{"), "{rendered}");
        assert!(!crate::formula::contains_quantifier(&prepared.expression));
        assert!(rendered.contains("A"), "{rendered}");
        assert!(rendered.contains("b = A"), "{rendered}");
        assert_eq!(prepared.side_conditions.len(), 1);
        assert!(matches!(
            prepared.side_conditions[0].introduced_type,
            TypeExpr::Matrix(_, _)
        ));
        let TypeExpr::Matrix(_, witness_cols) = &prepared.side_conditions[0].introduced_type else {
            unreachable!()
        };
        assert!(matches!(witness_cols.raw, RawExpr::NatLiteral(1)));
        assert!(matches!(
            prepared.side_conditions[0].existence,
            crate::visit_mut::Existence::Guaranteed
        ));
        assert!(prepared.side_conditions[0].defining_assertions.is_empty());
        assert_eq!(prepared.expression.meta.alternatives().len(), 1);
        assert!(matches!(
            prepared.expression.meta.alternatives()[0].raw,
            RawExpr::Finop(Finop::Exists, _)
        ));
    }

    #[test]
    fn negative_range_membership_lowers_through_a_counterexample() {
        let givens = [
            parse(r"A \in \mathbb{R}^{m \times n}"),
            parse(r"b \in \mathbb{R}^{m}"),
        ];
        let types = infer_symbolic_type_environment(&givens).unwrap();
        let prepared = prepare_expression(
            &types,
            &parse(r"b \in \operatorname{Range}(A)"),
            VisitContext::negative(),
        )
        .unwrap();
        assert!(!crate::formula::contains_quantifier(&prepared.expression));
        assert_eq!(prepared.side_conditions.len(), 1);
        assert!(
            prepared.side_conditions[0]
                .introduced_variable
                .name
                .contains(r"\operatorname{counterexample}")
        );
        assert!(
            prepared
                .expression
                .as_latex()
                .to_string()
                .contains(r"\implies")
        );

        let not_member = prepare(
            r"b \notin \operatorname{Range}(A)",
            &[r"A \in \mathbb{R}^{m \times n}", r"b \in \mathbb{R}^{m}"],
        )
        .unwrap();
        assert!(!crate::formula::contains_quantifier(&not_member.expression));
        assert_eq!(not_member.side_conditions.len(), 1);
        assert!(matches!(
            not_member.expression.raw,
            RawExpr::Monop(crate::Monop::Not, _)
        ));
    }

    #[test]
    fn positive_exists_lowers_and_negative_exists_is_rejected() {
        let tex = r"\exists w \in \mathbb{R}^{n}, A w = b";
        let givens = [r"A \in \mathbb{R}^{m \times n}", r"b \in \mathbb{R}^{m}"];
        let positive = prepare(tex, &givens).unwrap();
        assert!(
            !positive
                .expression
                .as_latex()
                .to_string()
                .contains(r"\exists")
        );
        assert_eq!(positive.side_conditions.len(), 1);
        assert!(!crate::formula::contains_quantifier(&positive.expression));
        assert!(
            positive.side_conditions[0]
                .introduced_variable
                .name
                .contains(r"\operatorname{witness}")
        );

        for scalar in [r"\exists a, a > 0", r"\exists a \in \mathbb{R}, a > 0"] {
            let prepared = prepare(scalar, &[]).unwrap();
            assert_eq!(prepared.side_conditions.len(), 1);
            assert_eq!(prepared.side_conditions[0].introduced_type, TypeExpr::Real);
        }

        let parsed_givens = givens.iter().map(|s| parse(s)).collect::<Vec<_>>();
        let types = infer_symbolic_type_environment(&parsed_givens).unwrap();
        let negative = prepare_expression(&types, &parse(tex), VisitContext::negative());
        assert!(matches!(
            negative,
            Err(TypeError::Unsupported(
                "existential expressions can only be lowered in positive logical contexts"
            ))
        ));
    }

    #[test]
    fn exists_rejects_multiple_typed_binders() {
        for tex in [
            r"\exists u \in \mathbb{R}^{n}, v \in \mathbb{R}^{n}, u = v",
            r"\exists u, v, u = v",
        ] {
            assert!(matches!(
                prepare(tex, &[]),
                Err(TypeError::Unsupported(
                    "quantifier lowering supports exactly one binder"
                ))
            ));
        }
        assert!(matches!(
            prepare(r"\exists w, w > 0", &[r"w \in \mathbb{R}"]),
            Err(TypeError::Invalid("quantifier binder must be fresh"))
        ));
    }

    #[test]
    fn exists_respects_logical_polarity() {
        let givens = [
            r"P \in \mathbb{B}",
            r"A \in \mathbb{R}^{m \times n}",
            r"b \in \mathbb{R}^{m}",
        ];
        let consequent = prepare(
            r"P \implies \left(\exists w \in \mathbb{R}^{n}, A w = b\right)",
            &givens,
        )
        .unwrap();
        assert_eq!(consequent.side_conditions.len(), 1);
        assert!(!crate::formula::contains_quantifier(&consequent.expression));

        let antecedent = prepare(
            r"\left(\exists w \in \mathbb{R}^{n}, A w = b\right) \implies P",
            &givens,
        );
        assert!(matches!(
            antecedent,
            Err(TypeError::Unsupported(
                "existential expressions can only be lowered in positive logical contexts"
            ))
        ));
    }

    #[test]
    fn negative_forall_lowers_bare_and_explicit_binders() {
        for tex in [r"\forall a, a = a", r"\forall a \in \mathbb{R}, a = a"] {
            let parsed = parse(tex);
            let types = infer_symbolic_type_environment(&[]).unwrap();
            let prepared = prepare_expression(&types, &parsed, VisitContext::negative()).unwrap();
            assert!(!crate::formula::contains_quantifier(&prepared.expression));
            assert_eq!(prepared.side_conditions.len(), 1);
            assert_eq!(prepared.side_conditions[0].introduced_type, TypeExpr::Real);
            assert!(
                prepared.side_conditions[0]
                    .introduced_variable
                    .name
                    .contains(r"\operatorname{counterexample}")
            );
        }
    }

    #[test]
    fn negative_forall_preserves_premise_implication_semantics() {
        let types = infer_symbolic_type_environment(&[]).unwrap();
        let prepared = prepare_expression(
            &types,
            &parse(r"\forall a, a > 0, a > 1"),
            VisitContext::negative(),
        )
        .unwrap();
        let rendered = prepared.expression.as_latex().to_string();
        assert!(rendered.contains(r"\implies"), "{rendered}");
        assert!(matches!(
            prepared.expression.raw,
            RawExpr::LogicChain(crate::LogicChain { ref assertions, .. })
                if matches!(assertions.as_slice(), [(crate::Logic::Imp, _)])
        ));

        let positive = prepare_expression(
            &types,
            &parse(r"\forall a, a = a"),
            VisitContext::positive(),
        );
        assert!(matches!(
            positive,
            Err(TypeError::Unsupported(
                "universal expressions can only be lowered in negative logical contexts"
            ))
        ));
    }

    #[test]
    fn exists_witnesses_are_lifted_under_sequence_ranges() {
        let prepared = prepare(
            r"\operatorname{map}_{i=1}^{n}\left(\exists w \in \mathbb{R}, w > 0\right)",
            &[r"n = 2"],
        )
        .unwrap();
        assert_eq!(prepared.side_conditions.len(), 1);
        let TypeExpr::Seq(element, length) = &prepared.side_conditions[0].introduced_type else {
            panic!("expected a sequence-valued witness")
        };
        assert!(matches!(element.raw, RawExpr::Type(TypeExpr::Real)));
        assert_eq!(length.as_latex().to_string(), "n - 1 + 1");
        assert_eq!(prepared.side_conditions[0].active_ranges.len(), 1);
    }

    #[test]
    fn repeated_exists_uses_one_deterministically_named_witness() {
        let quantified = r"\left(\exists w \in \mathbb{R}^{n}, A w = b\right)";
        let prepared = prepare(
            &format!(r"{quantified} \land {quantified}"),
            &[r"A \in \mathbb{R}^{m \times n}", r"b \in \mathbb{R}^{m}"],
        )
        .unwrap();
        assert_eq!(prepared.side_conditions.len(), 1);
        let name = &prepared.side_conditions[0].introduced_variable.name;
        assert!(name.contains(r"\operatorname{witness}"), "{name}");
        assert!(!name.contains("implicit_dimension"), "{name}");
    }

    #[test]
    fn rejects_unsupported_domains_and_predicates_but_defers_set_values() {
        for input in [
            r"1 \in \{x \in \mathbb{N} : x > 0\}",
            r"1 \in \{x \in \mathbb{R} : x\}",
        ] {
            assert!(prepare(input, &[]).is_err(), "{input}");
        }

        for prepared in [
            prepare(r"\{x \in \mathbb{R} : x > 0\}", &[]).unwrap(),
            prepare(
                r"\operatorname{Range}(A)",
                &[r"A \in \mathbb{R}^{2 \times 2}"],
            )
            .unwrap(),
            prepare(
                r"\{x \in \mathbb{R} : x > 0\} = \{x \in \mathbb{R} : x > 0\}",
                &[],
            )
            .unwrap(),
            prepare(
                r"y \in S",
                &[r"y \in \mathbb{R}", r"S \in \operatorname{Set}(\mathbb{R})"],
            )
            .unwrap(),
        ] {
            assert!(crate::to_z3::to_z3(&crate::Environment::default(), &prepared).is_err());
        }
    }
}
