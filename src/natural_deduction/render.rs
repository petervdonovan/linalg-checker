//! Presentation of one local inference. Rendering never consults a proof store.
use super::*;

fn bullets(expressions: &[Expr<()>]) -> String {
    expressions
        .iter()
        .map(|e| format!("- ${}$", e.as_latex()))
        .collect::<Vec<_>>()
        .join("\n")
}
impl NaturalDeductionProof {
    fn rule_label(&self) -> &'static str {
        match self {
            Self::Reuse {
                kind: ReuseKind::Elaborated,
                ..
            } => "\\text{elaboration}",
            Self::Reuse { .. } => "\\text{reuse}",
            Self::ConjunctionIntroduction { .. } => "\\land I",
            Self::ConjunctionElimination { .. } => "\\land E",
            Self::ExistentialIntroduction { .. } => "\\exists I",
            Self::ExistentialElimination { .. } => "\\text{witness opening}",
            Self::UniversalIntroduction { .. } => "\\forall I",
            Self::UniversalElimination { .. } => "\\forall E",
            Self::ImplicationIntroduction { .. } => "\\Rightarrow I",
            Self::Assumption { .. } => "assumption",
            Self::External | Self::ScopedGoal { .. } => "established",
        }
    }
    fn discharged_formulas(&self) -> Vec<(AssumptionId, &Expr<()>)> {
        match self {
            Self::ImplicationIntroduction {
                discharged_formulas,
                ..
            }
            | Self::UniversalIntroduction {
                discharged_formulas,
                ..
            } => discharged_formulas.iter().map(|(id, e)| (*id, e)).collect(),
            _ => vec![],
        }
    }
    /// Stable preorder labels for this local proof, never archived derivations.
    fn all_discharged(&self) -> Vec<(AssumptionId, &Expr<()>)> {
        fn visit<'a>(
            proof: &'a NaturalDeductionProof,
            result: &mut Vec<(AssumptionId, &'a Expr<()>)>,
        ) {
            for (id, formula) in proof.discharged_formulas() {
                if !result.iter().any(|(old, _)| *old == id) {
                    result.push((id, formula));
                }
            }
            for input in proof.inputs() {
                if let ProofInput::Local { proof, .. } = input {
                    visit(proof, result);
                }
            }
        }
        let mut result = Vec::new();
        visit(self, &mut result);
        result
    }
    /// A math-mode fragment showing this step only. Context facts are leaves.
    pub fn to_tex(&self, conclusion: &Expr<()>) -> String {
        self.tree_tex(conclusion, &self.all_discharged(), &BTreeSet::new())
    }
    fn tree_tex(
        &self,
        conclusion: &Expr<()>,
        legend: &[(AssumptionId, &Expr<()>)],
        ancestors: &BTreeSet<AssumptionId>,
    ) -> String {
        let own = self.discharged_formulas();
        let mut active = ancestors.clone();
        active.extend(own.iter().map(|(id, _)| *id));
        let label = |id: AssumptionId| {
            legend
                .iter()
                .position(|(a, _)| *a == id)
                .map(|i| format!("a_{{{}}}", i + 1))
        };
        let leaf = |formula: &Expr<()>, id: Option<AssumptionId>| {
            if let Some(id) = id
                && active.contains(&id)
                && let Some(label) = label(id)
            {
                format!("\\left[{}\\right]^{{{label}}}", formula.as_latex())
            } else {
                formula.as_latex().to_string()
            }
        };
        match self {
            Self::Assumption { assumption } => return leaf(conclusion, Some(*assumption)),
            Self::External | Self::ScopedGoal { .. } => return conclusion.as_latex().to_string(),
            _ => (),
        }
        let numerator = self
            .inputs()
            .iter()
            .map(|input| match input {
                ProofInput::Context(p) => leaf(&p.expression, p.assumption),
                ProofInput::Local { conclusion, proof } => {
                    proof.tree_tex(conclusion, legend, &active)
                }
            })
            .collect::<Vec<_>>()
            .join(" \\qquad ");
        let suffix = match self {
            Self::ConjunctionElimination { operand, .. } => format!("_{{{}}}", operand + 1),
            Self::ImplicationIntroduction { .. } | Self::UniversalIntroduction { .. }
                if !own.is_empty() =>
            {
                format!(
                    "\\,[{}]",
                    own.iter()
                        .filter_map(|(id, _)| label(*id))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            _ => String::new(),
        };
        format!(
            "\\dfrac{{{numerator}}}{{{}}}\\;({}{suffix})",
            conclusion.as_latex(),
            self.rule_label()
        )
    }
    /// Shared Markdown details, omitting trivial contextual-reuse trees.
    pub fn details(&self, conclusion: &Expr<()>) -> String {
        let facts = self.supporting_facts();
        let inference = self.inference();
        let detail = match inference {
            Self::Reuse {
                kind: ReuseKind::Literal,
                ..
            } => "This statement is already established in the current context.".to_owned(),
            Self::Reuse { kind, .. } => format!(
                "{}:\n\n{}",
                if *kind == ReuseKind::Elaborated {
                    "Established fact (using its elaborated form)"
                } else {
                    "Established fact"
                },
                bullets(&facts)
            ),
            Self::ExistentialIntroduction { assignments, .. } => format!(
                "Witness:\n\n{}\n\nMatched facts:\n\n{}",
                assignments
                    .iter()
                    .map(|(v, e)| format!("- ${} = {}$", v.z3_name(), e.as_latex()))
                    .collect::<Vec<_>>()
                    .join("\n"),
                bullets(&facts)
            ),
            Self::ExistentialElimination {
                source,
                assignments,
                ..
            } => format!(
                "From ${}$:\n\n{}",
                source.leaves()[0].expression.as_latex(),
                assignments
                    .iter()
                    .map(|(binder, witness)| format!(
                        "- ${}$ as a witness for ${}$",
                        witness.z3_name(),
                        binder.z3_name()
                    ))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            _ => {
                let mut text = match inference {
                    Self::UniversalElimination { assignments, .. } => assignments
                        .iter()
                        .map(|(v, e)| format!("- ${} = {}$", v.z3_name(), e.as_latex()))
                        .collect::<Vec<_>>()
                        .join("\n"),
                    Self::UniversalIntroduction {
                        assignments,
                        discharged,
                        ..
                    } => format!(
                        "Generalized {} parameter(s), discharging {} assumption(s).\n\n{}",
                        assignments.len(),
                        discharged.len(),
                        assignments
                            .iter()
                            .map(|(v, p)| format!(
                                "- ${}$ generalized as ${}$",
                                p.z3_name(),
                                v.z3_name()
                            ))
                            .collect::<Vec<_>>()
                            .join("\n")
                    ),
                    Self::ImplicationIntroduction { discharged, .. } => {
                        format!(
                            "Discharged {} assumption(s){}.",
                            discharged.len(),
                            if self.all_discharged().len() > discharged.len() {
                                " at the final inference"
                            } else {
                                ""
                            }
                        )
                    }
                    Self::ConjunctionIntroduction { .. } => {
                        "Combined the established conjuncts.".to_owned()
                    }
                    Self::ConjunctionElimination { operand, .. } => {
                        format!("Selected conjunct {}.", operand + 1)
                    }
                    _ => String::new(),
                };
                let discharged = self.all_discharged();
                if !discharged.is_empty() {
                    text.push_str("\n\nDischarged assumptions:\n\n");
                    text.push_str(
                        &discharged
                            .iter()
                            .enumerate()
                            .map(|(i, (_, e))| format!("- $a_{{{}}}$: ${}$", i + 1, e.as_latex()))
                            .collect::<Vec<_>>()
                            .join("\n"),
                    );
                }
                if !facts.is_empty() {
                    text.push_str(&format!("\n\nSupporting facts:\n\n{}", bullets(&facts)));
                }
                text
            }
        };
        if matches!(
            self,
            Self::Reuse {
                premise: ProofInput::Context(_),
                kind: ReuseKind::Literal | ReuseKind::Resolved,
            }
        ) {
            return detail;
        }
        format!(
            "{detail}\n\nProof tree:\n\n$$\n{}\n$$",
            self.to_tex(conclusion)
        )
    }
}
