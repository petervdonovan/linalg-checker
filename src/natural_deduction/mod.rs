//! One-step natural deduction over established facts. Matching never searches
//! recursively or calls an SMT solver. Type/dimension obligations are delegated
//! to a deliberately restricted side-condition interface.
use crate::{
    Expr, Finop, ImplicitDimension, Logic, RawExpr, TypeExpr, Variable,
    formula::{conjunction_views, free_variables},
    type_resolver::SymbolicTypeEnvironment,
};
use std::collections::{BTreeMap, BTreeSet};
mod context;
mod matching;

mod rules;
pub use crate::type_resolver::{QuantifierKind, QuantifierSpec, analyze_quantifier};
pub use context::*;
use matching::{Match, match_requirements};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Premise {
    pub fact: FactId,
    pub derivation: DerivationId,
    /// Original source retained even after its lexical scope has closed.
    pub expression: Expr<()>,
    /// None means the original expression; Some indexes an elaborated alternative.
    pub alternative: Option<usize>,
    /// Index in the deterministic, depth-first conjunction views (zero is whole).
    pub conjunct: usize,
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
        premise: Premise,
    },
    ExistentialIntroduction {
        premises: Vec<Premise>,
        assignments: BTreeMap<Variable, Expr<()>>,
    },
    /// Opens a witness scope; recording the result creates its assumption.
    ExistentialElimination {
        source: Premise,
        assignments: BTreeMap<Variable, Variable>,
        introduced_types: BTreeMap<Variable, TypeExpr<()>>,
    },
    UniversalElimination {
        source: Premise,
        premises: Vec<Premise>,
        assignments: BTreeMap<Variable, Expr<()>>,
    },
    UniversalIntroduction {
        premise: Premise,
        assignments: BTreeMap<Variable, Variable>,
        discharged: BTreeSet<AssumptionId>,
    },
    ImplicationIntroduction {
        premise: Premise,
        discharged: BTreeSet<AssumptionId>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NaturalDeductionResult {
    Established { derivations: Vec<Derivation> },
    NoMatch,
    Inconclusive { reasons: Vec<String> },
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
    checks: &mut impl SideConditionChecker,
) -> NaturalDeductionResult {
    let analysis = crate::type_resolver::analyze_formula(&context.types, conclusion);
    if let Err(error) = &analysis
        && !matches!(
            error,
            crate::type_resolver::TypeError::MissingType(_)
                | crate::type_resolver::TypeError::UndefinedVariable(_)
        )
    {
        return NaturalDeductionResult::Inconclusive {
            reasons: vec![error.to_string()],
        };
    }
    let result = rules::check(context, conclusion, checks);
    if analysis.is_err()
        && let NaturalDeductionResult::Established { derivations } = result
    {
        let derivations = derivations
            .into_iter()
            .filter(|d| {
                let NaturalDeductionProof::ExistentialElimination {
                    introduced_types, ..
                } = &d.proof
                else {
                    return false;
                };
                let mut scope = context.types.clone();
                scope.types.extend(introduced_types.clone());
                crate::type_resolver::analyze_formula(&scope, conclusion).is_ok()
            })
            .collect::<Vec<_>>();
        if derivations.is_empty() {
            NaturalDeductionResult::Inconclusive {
                reasons: vec![analysis.unwrap_err().to_string()],
            }
        } else {
            NaturalDeductionResult::Established { derivations }
        }
    } else {
        result
    }
}

#[cfg(test)]
mod tests;
