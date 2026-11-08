//! Local natural deduction over established facts. Conjunction matching may
//! recurse, but never chains implication/quantifier rules or calls an SMT solver.
//! Type/dimension obligations are delegated
//! to a deliberately restricted side-condition interface.
use crate::{
    Expr, Finop, ImplicitDimension, Logic, RawExpr, TypeExpr, Variable,
    formula::{conjunction_views, free_variables},
    type_resolver::SymbolicTypeEnvironment,
};
use std::collections::{BTreeMap, BTreeSet};
mod checked;
mod context;
pub use checked::{CheckedFormula, FormulaInterpreter, SurfaceInterpreter};
mod matching;

mod proof;
mod render;
mod rules;
pub mod smt_backend;
pub use crate::type_resolver::{QuantifierKind, QuantifierSpec, analyze_quantifier};
pub use context::*;
use matching::{Match, match_requirements};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Premise {
    pub fact: FactId,
    pub derivation: DerivationId,
    /// Identity when this contextual leaf is itself an open assumption.
    pub assumption: Option<AssumptionId>,
    /// Original source retained even after its lexical scope has closed.
    pub expression: Expr<()>,
    /// None means the original expression; Some indexes an elaborated alternative.
    pub alternative: Option<usize>,
    /// Internal matching-view index. Materialized proof leaves always use zero.
    pub conjunct: usize,
}
/// Evidence for an input to the current inference. Context leaves are never expanded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofInput {
    Context(Premise),
    Local {
        conclusion: Expr<()>,
        proof: Box<NaturalDeductionProof>,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReuseKind {
    Literal,
    Resolved,
    Elaborated,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NaturalDeductionProof {
    Assumption {
        assumption: AssumptionId,
    },
    External,
    /// Existing Markdown-driven discharge/generalization, outside rule search.
    ScopedGoal {
        givens: Vec<Expr<()>>,
        conclusion: Expr<()>,
        cases: Vec<DerivationId>,
    },
    Reuse {
        premise: ProofInput,
        kind: ReuseKind,
    },
    ConjunctionIntroduction {
        premises: Vec<ProofInput>,
    },
    ConjunctionElimination {
        premise: ProofInput,
        /// Zero-based immediate operand index. Nested projections form a chain.
        operand: usize,
    },
    DisjunctionIntroduction {
        premise: ProofInput,
        /// Zero-based first matching immediate disjunct, retained as evidence.
        operand: usize,
    },
    ExistentialIntroduction {
        premises: Vec<ProofInput>,
        assignments: BTreeMap<Variable, Expr<()>>,
    },
    /// Opens a witness scope; recording the result creates its assumption.
    ExistentialElimination {
        source: ProofInput,
        assignments: BTreeMap<Variable, Variable>,
        introduced_types: BTreeMap<Variable, TypeExpr<()>>,
    },
    UniversalElimination {
        source: ProofInput,
        premises: Vec<ProofInput>,
        assignments: BTreeMap<Variable, Expr<()>>,
    },
    UniversalIntroduction {
        premise: ProofInput,
        assignments: BTreeMap<Variable, Variable>,
        discharged: BTreeSet<AssumptionId>,
        discharged_formulas: BTreeMap<AssumptionId, Expr<()>>,
    },
    ImplicationIntroduction {
        premise: ProofInput,
        discharged: BTreeSet<AssumptionId>,
        discharged_formulas: BTreeMap<AssumptionId, Expr<()>>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NaturalDeductionResult {
    Established {
        conclusion: CheckedFormula,
        derivations: Vec<Derivation>,
    },
    NoMatch {
        conclusion: CheckedFormula,
    },
    Inconclusive {
        conclusion: CheckedFormula,
        reasons: Vec<String>,
    },
    Invalid {
        error: crate::type_resolver::TypeError,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SideConditionResult {
    Valid,
    Invalid,
    Inconclusive(String),
}

pub trait SideConditionChecker {
    /// Context derivations used by the most recent successful side-condition check.
    /// These carry scope dependencies, never verification-status qualifications.
    fn premise_derivations(&self) -> &[DerivationId] {
        &[]
    }
    /// Check typing and dimension relationships for an already matched instance.
    /// This is not permission to establish missing logical premises.
    fn check_instantiation(
        &mut self,
        spec: &QuantifierSpec,
        assignments: &BTreeMap<Variable, Expr<()>>,
        nonce_pairs: &BTreeSet<(ImplicitDimension, ImplicitDimension)>,
        supporting_facts: &[Expr<()>],
    ) -> SideConditionResult;
}

/// Returns all nondominated justifications, without changing `context`.
/// Conjunction projections and trusted elaborations count as context views.
pub fn follows_from_natural_deduction(
    context: &ProofContext,
    conclusion: &Expr<()>,
    interpreter: &impl FormulaInterpreter,
    checks: &mut impl SideConditionChecker,
) -> NaturalDeductionResult {
    match interpreter.check(context, conclusion) {
        Ok(checked) => {
            let spec = if crate::formula::is_quantifier(checked.analyzed()) {
                Some(
                    QuantifierSpec::from_analyzed(checked.analyzed())
                        .expect("checked quantifiers have binding metadata"),
                )
            } else {
                None
            };
            let result = rules::check(
                context,
                &checked.meaning(),
                checked.free_variables(),
                spec.as_ref(),
                checks,
            );
            attach_checked(checked, result)
        }
        Err(error) => {
            for (source_id, introduced_types) in rules::witness_scopes(context, conclusion) {
                let mut scope = context.clone();
                scope.enter_scope();
                for (v, t) in &introduced_types {
                    scope.declare_parameter(v.clone(), t.clone());
                }
                if let Ok(checked)=interpreter.check(&scope,conclusion)
                    && let rules::RuleResult::Established(derivations)=rules::check(context,&checked.meaning(),checked.free_variables(),None,checks)
                    && let Some(source)=derivations.into_iter().find(|d|matches!(&d.proof,NaturalDeductionProof::ExistentialElimination{source,introduced_types:verified,..} if source.leaves()[0].derivation==source_id && *verified==introduced_types)) {
                    return NaturalDeductionResult::Established{conclusion:checked,derivations:vec![source]};
                }
            }
            NaturalDeductionResult::Invalid { error }
        }
    }
}
fn attach_checked(conclusion: CheckedFormula, result: rules::RuleResult) -> NaturalDeductionResult {
    let result = if let rules::RuleResult::Established(mut derivations) = result {
        for d in &mut derivations {
            if let NaturalDeductionProof::Reuse {
                premise: ProofInput::Context(premise),
                kind,
            } = &mut d.proof
            {
                *kind = if premise.alternative.is_some() {
                    ReuseKind::Elaborated
                } else if premise.expression == *conclusion.written() {
                    ReuseKind::Literal
                } else {
                    ReuseKind::Resolved
                };
            }
        }
        rules::RuleResult::Established(derivations)
    } else {
        result
    };
    match result {
        rules::RuleResult::Established(derivations) => NaturalDeductionResult::Established {
            conclusion,
            derivations,
        },
        rules::RuleResult::NoMatch => NaturalDeductionResult::NoMatch { conclusion },
        rules::RuleResult::Inconclusive(reasons) => NaturalDeductionResult::Inconclusive {
            conclusion,
            reasons,
        },
    }
}
impl NaturalDeductionResult {
    pub fn checked(&self) -> Option<&CheckedFormula> {
        match self {
            Self::Established { conclusion, .. } | Self::NoMatch { conclusion } => Some(conclusion),
            Self::Inconclusive { conclusion, .. } => Some(conclusion),
            Self::Invalid { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests;
