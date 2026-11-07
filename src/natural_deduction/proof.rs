use super::*;

impl ProofInput {
    pub fn conclusion(&self) -> &Expr<()> {
        match self {
            Self::Context(p) => &p.expression,
            Self::Local { conclusion, .. } => conclusion,
        }
    }
    pub fn leaves(&self) -> Vec<&Premise> {
        match self {
            Self::Context(p) => vec![p],
            Self::Local { proof, .. } => proof.leaves(),
        }
    }
    pub(crate) fn local(conclusion: Expr<()>, proof: NaturalDeductionProof) -> Self {
        Self::Local {
            conclusion,
            proof: Box::new(proof),
        }
    }
}
impl NaturalDeductionProof {
    /// The rule justifying this step, beneath any final checked elaboration view.
    pub fn inference(&self) -> &Self {
        match self {
            Self::Reuse {
                kind: ReuseKind::Elaborated,
                premise: ProofInput::Local { proof, .. },
            } => proof.inference(),
            _ => self,
        }
    }
    pub fn inputs(&self) -> Vec<&ProofInput> {
        match self {
            Self::Reuse { premise, .. }
            | Self::ConjunctionElimination { premise, .. }
            | Self::UniversalIntroduction { premise, .. }
            | Self::ImplicationIntroduction { premise, .. } => vec![premise],
            Self::ConjunctionIntroduction { premises }
            | Self::ExistentialIntroduction { premises, .. } => premises.iter().collect(),
            Self::ExistentialElimination { source, .. } => vec![source],
            Self::UniversalElimination {
                source, premises, ..
            } => std::iter::once(source).chain(premises).collect(),
            _ => vec![],
        }
    }
    /// Contextual references only; never follows their archived derivations.
    pub fn leaves(&self) -> Vec<&Premise> {
        self.inputs()
            .into_iter()
            .flat_map(ProofInput::leaves)
            .collect()
    }
    pub fn supporting_facts(&self) -> Vec<Expr<()>> {
        let mut facts = Vec::new();
        for p in self.leaves() {
            if !facts.contains(&p.expression) {
                facts.push(p.expression.clone());
            }
        }
        facts
    }
    pub fn references(&self) -> Vec<DerivationId> {
        let mut refs = self
            .leaves()
            .iter()
            .map(|p| p.derivation)
            .collect::<Vec<_>>();
        if let Self::ScopedGoal { cases, .. } = self {
            refs.extend(cases);
        }
        for input in self.inputs() {
            if let ProofInput::Local { proof, .. } = input {
                for id in proof.references() {
                    if !refs.contains(&id) {
                        refs.push(id);
                    }
                }
            }
        }
        refs
    }
}

/// Materialize the conjunction path selected by a matching view. The original
/// contextual statement remains a leaf even if its own proof was complex.
pub(crate) fn view_input(context: &ProofContext, view: &Premise) -> ProofInput {
    let mut whole = view.clone();
    whole.conjunct = 0;
    let expression = context
        .analyzed_view(&whole)
        .expect("checked context view")
        .with_default_metadata();
    let leaf = ProofInput::Context(whole);
    let fact = context
        .facts
        .iter()
        .find(|f| f.id == view.fact)
        .expect("visible fact");
    let mut input = if view.alternative.is_some() {
        ProofInput::local(
            expression.clone(),
            NaturalDeductionProof::Reuse {
                premise: leaf,
                kind: ReuseKind::Elaborated,
            },
        )
    } else if expression != fact.expression {
        ProofInput::local(
            expression.clone(),
            NaturalDeductionProof::Reuse {
                premise: leaf,
                kind: ReuseKind::Resolved,
            },
        )
    } else {
        leaf
    };
    fn path(
        expression: &Expr<()>,
        target: usize,
        cursor: &mut usize,
        indices: &mut Vec<usize>,
    ) -> bool {
        if *cursor == target {
            return true;
        }
        *cursor += 1;
        if let RawExpr::Finop(Finop::And, operands) = &expression.raw {
            for (i, operand) in operands.iter().enumerate() {
                indices.push(i);
                if path(operand, target, cursor, indices) {
                    return true;
                }
                indices.pop();
            }
        }
        false
    }
    let mut indices = Vec::new();
    assert!(path(&expression, view.conjunct, &mut 0, &mut indices));
    let mut expression = &expression;
    for operand in indices {
        let RawExpr::Finop(Finop::And, operands) = &expression.raw else {
            unreachable!()
        };
        expression = &operands[operand];
        input = ProofInput::local(
            expression.clone(),
            NaturalDeductionProof::ConjunctionElimination {
                premise: input,
                operand,
            },
        );
    }
    input
}
