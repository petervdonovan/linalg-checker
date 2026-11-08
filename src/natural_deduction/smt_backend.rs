//! Standalone bounded conjunction-introduction search. The budget counts distinct
//! reachable non-leaf proof values, numbered in canonical BFS order. Context facts
//! stay leaves, and finding a proof never commits it to the context.
use super::*;
use crate::smt_dt::{self, ExprDatatype, ProofDatatype, ProofNode, ProofRule};
use std::{
    fmt,
    sync::atomic::{AtomicU64, Ordering},
};
use z3::{
    Params, SatResult, Solver,
    ast::{Ast, Datatype},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SearchLimits {
    /// Maximum distinct reachable non-leaf proof values. Shared subproofs count once.
    pub max_rule_slots: usize,
    /// Maximum premises at an inference; list cells do not consume slots.
    pub max_premises: usize,
    /// None is unlimited. Some(0) is rejected to avoid Z3's unlimited-zero policy.
    pub timeout_ms: Option<u32>,
}
#[derive(Debug)]
pub enum SearchError {
    InvalidConclusion(crate::type_resolver::TypeError),
    Encoding(smt_dt::Error),
    InvalidOptions(&'static str),
    NoProofWithinBounds(SearchLimits),
    Timeout { reason: String },
    Unknown { reason: String },
    InvalidModel(String),
}
impl fmt::Display for SearchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConclusion(e) => write!(f, "invalid conclusion: {e}"),
            Self::Encoding(e) => e.fmt(f),
            Self::InvalidOptions(s) => write!(f, "invalid search options: {s}"),
            Self::NoProofWithinBounds(l) => write!(
                f,
                "no proof within encoding and budget ({} rule slots, {} premises)",
                l.max_rule_slots, l.max_premises
            ),
            Self::Timeout { reason } => write!(f, "proof search timed out: {reason}"),
            Self::Unknown { reason } => write!(f, "proof search returned unknown: {reason}"),
            Self::InvalidModel(s) => write!(f, "invalid proof model: {s}"),
        }
    }
}
impl std::error::Error for SearchError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidConclusion(e) => Some(e),
            Self::Encoding(e) => Some(e),
            _ => None,
        }
    }
}
impl From<smt_dt::Error> for SearchError {
    fn from(value: smt_dt::Error) -> Self {
        Self::Encoding(value)
    }
}
fn model_error(e: smt_dt::Error) -> SearchError {
    SearchError::InvalidModel(e.to_string())
}
fn check_status(
    result: SatResult,
    reason: Option<String>,
    limits: SearchLimits,
) -> Result<(), SearchError> {
    match result {
        SatResult::Sat => Ok(()),
        SatResult::Unsat => Err(SearchError::NoProofWithinBounds(limits)),
        SatResult::Unknown => {
            let reason = reason.unwrap_or_else(|| "no diagnostic supplied".into());
            if reason.to_ascii_lowercase().contains("timeout") {
                Err(SearchError::Timeout { reason })
            } else {
                Err(SearchError::Unknown { reason })
            }
        }
    }
}

struct Leaf {
    value: Datatype,
    premise: Premise,
}
struct Query<'a> {
    context: &'a ProofContext,
    checked: CheckedFormula,
    limits: SearchLimits,
    expressions: ExprDatatype,
    proofs: ProofDatatype,
    solver: Solver,
    root: Datatype,
    target: Datatype,
    leaves: Vec<Leaf>,
}
impl<'a> Query<'a> {
    fn new(
        context: &'a ProofContext,
        conclusion: &Expr<()>,
        interpreter: &impl FormulaInterpreter,
        limits: SearchLimits,
    ) -> Result<Self, SearchError> {
        if limits.timeout_ms == Some(0) {
            return Err(SearchError::InvalidOptions(
                "zero timeout means unlimited in Z3; use None",
            ));
        }
        let checked = interpreter
            .check(context, conclusion)
            .map_err(SearchError::InvalidConclusion)?;
        // Codecs have independent intern tables, so each search needs its own
        // namespace in the shared thread-local Z3 context. IDs are not rendered.
        static NEXT_QUERY: AtomicU64 = AtomicU64::new(0);
        let id = NEXT_QUERY.fetch_add(1, Ordering::Relaxed);
        let namespace = format!("nd_search_{id}");
        let mut expressions = ExprDatatype::new(&format!("{namespace}.expr"));
        let proofs = ProofDatatype::new(&format!("{namespace}.proof"), &expressions);
        let target = expressions.encode(&checked.meaning())?;
        let mut leaves: Vec<Leaf> = Vec::new();
        for fact in context.facts() {
            let derivation = fact
                .derivations()
                .next()
                .expect("accepted facts have derivations");
            let premise = Premise {
                fact: fact.id(),
                derivation: derivation.id,
                assumption: match derivation.proof {
                    NaturalDeductionProof::Assumption { assumption } => Some(assumption),
                    _ => None,
                },
                expression: fact.formula().written().clone(),
                alternative: None,
                conjunct: 0,
            };
            let meaning: Expr<()> = context
                .analyzed_view(&premise)
                .expect("visible fact has checked bindings")
                .with_default_metadata();
            let value = proofs.context(&expressions.encode(&meaning)?)?;
            if !leaves.iter().any(|l| l.value == value) {
                leaves.push(Leaf { value, premise });
            }
        }
        let solver = Solver::new_for_logic("QF_DT")
            .ok_or(SearchError::InvalidOptions("QF_DT solver unavailable"))?;
        if let Some(timeout) = limits.timeout_ms {
            let mut params = Params::new();
            params.set_u32("timeout", timeout);
            solver.set_params(&params);
        }
        let root = proofs.constant(format!("{namespace}.root"));
        let slots = (0..limits.max_rule_slots)
            .map(|i| proofs.constant(format!("{namespace}.slot_{i}")))
            .collect::<Vec<_>>();
        let leaf_values = leaves.iter().map(|l| l.value.clone()).collect::<Vec<_>>();
        solver.assert(proofs.bounded_structure(
            &root,
            &slots,
            &leaf_values,
            limits.max_premises,
        )?);
        solver.assert(proofs.rule_constraints(&expressions, &slots, limits.max_premises)?);
        solver.assert(proofs.conclusion(&root)?.eq(&target));
        Ok(Self {
            context,
            checked,
            limits,
            expressions,
            proofs,
            solver,
            root,
            target,
            leaves,
        })
    }
    fn decode_value(
        &self,
        value: &Datatype,
        remaining_depth: usize,
    ) -> Result<ProofInput, SearchError> {
        match self.proofs.inspect(value).map_err(model_error)? {
            ProofNode::Unused => Err(SearchError::InvalidModel("unused proof node".into())),
            ProofNode::Context { conclusion } => {
                let leaf = self
                    .leaves
                    .iter()
                    .find(|l| l.value == *value)
                    .ok_or_else(|| SearchError::InvalidModel("unknown contextual leaf".into()))?;
                let mut input = super::proof::view_input(self.context, &leaf.premise);
                let meaning = self.expressions.decode(&conclusion).map_err(model_error)?;
                // Expression encoding intentionally resolves comparison chains.
                // Preserve that structural view explicitly rather than changing a fact.
                if input.conclusion() != &meaning {
                    input = ProofInput::local(
                        meaning,
                        NaturalDeductionProof::Reuse {
                            premise: input,
                            kind: ReuseKind::Resolved,
                        },
                    );
                }
                Ok(input)
            }
            ProofNode::Inference {
                conclusion,
                rule: ProofRule::AndIntroduction,
                premises,
            } => {
                if remaining_depth == 0 {
                    return Err(SearchError::InvalidModel(
                        "inference depth exceeds slot budget".into(),
                    ));
                }
                let premises = self
                    .proofs
                    .read_premises(&premises, self.limits.max_premises)
                    .map_err(model_error)?;
                if premises.is_empty() {
                    return Err(SearchError::InvalidModel(
                        "empty conjunction introduction".into(),
                    ));
                }
                let inputs = premises
                    .iter()
                    .map(|p| self.decode_value(p, remaining_depth - 1))
                    .collect::<Result<Vec<_>, _>>()?;
                let meaning = self.expressions.decode(&conclusion).map_err(model_error)?;
                let expected = Expr::new(RawExpr::Finop(
                    Finop::And,
                    inputs.iter().map(|p| p.conclusion().clone()).collect(),
                ));
                if meaning != expected {
                    return Err(SearchError::InvalidModel(
                        "conjunction conclusion differs from premises".into(),
                    ));
                }
                Ok(ProofInput::local(
                    meaning,
                    NaturalDeductionProof::ConjunctionIntroduction { premises: inputs },
                ))
            }
        }
    }
    fn decode(&self, model: &z3::Model) -> Result<Derivation, SearchError> {
        for assertion in self.solver.get_assertions() {
            if model.eval(&assertion, true).and_then(|b| b.as_bool()) != Some(true) {
                return Err(SearchError::InvalidModel(
                    "model does not satisfy proof query".into(),
                ));
            }
        }
        let root = model
            .eval(&self.root, true)
            .ok_or_else(|| SearchError::InvalidModel("root was not evaluated".into()))?;
        let conclusion = self
            .proofs
            .conclusion(&root)
            .map_err(model_error)?
            .simplify();
        if conclusion != self.target {
            return Err(SearchError::InvalidModel(
                "root conclusion differs from requested formula".into(),
            ));
        }
        let input = self.decode_value(&root, self.limits.max_rule_slots)?;
        let mut proof = match input {
            ProofInput::Context(premise) => NaturalDeductionProof::Reuse {
                premise: ProofInput::Context(premise),
                kind: ReuseKind::Resolved,
            },
            ProofInput::Local { proof, .. } => *proof,
        };
        if let NaturalDeductionProof::Reuse {
            premise: ProofInput::Context(p),
            kind,
        } = &mut proof
        {
            *kind = if p.expression == *self.checked.written() {
                ReuseKind::Literal
            } else {
                ReuseKind::Resolved
            };
        }
        let mut derivation = super::proof::derived(self.context, proof);
        self.context
            .refresh_scopes(&mut derivation, self.checked.free_variables());
        Ok(self
            .context
            .discharge_witnesses(self.checked.free_variables(), &derivation))
    }
}

/// Find one proof without changing the context. Accepted facts are leaves,
/// irrespective of how they were established. The caller explicitly records it.
pub fn find_proof(
    context: &ProofContext,
    conclusion: &Expr<()>,
    interpreter: &impl FormulaInterpreter,
    limits: SearchLimits,
) -> Result<(CheckedFormula, Derivation), SearchError> {
    let query = Query::new(context, conclusion, interpreter, limits)?;
    let status = query.solver.check();
    let reason = if status == SatResult::Unknown {
        query.solver.get_reason_unknown()
    } else {
        None
    };
    check_status(status, reason, limits)?;
    let model = query
        .solver
        .get_model()
        .ok_or_else(|| SearchError::InvalidModel("satisfiable query has no model".into()))?;
    let derivation = query.decode(&model)?;
    Ok((query.checked, derivation))
}

#[cfg(test)]
mod tests;
