//! Standalone bounded conjunction introduction/elimination and implication introduction with exact
//! assumption dependencies. The budget counts distinct
//! reachable non-leaf proof values, numbered in canonical BFS order. Context facts
//! stay leaves, and finding a proof never commits it to the context.
use super::*;
use crate::smt_dt::{
    self, AssumptionRef, ExprDatatype, ProofDatatype, ProofNode, ProofRule, at_most,
};
use crate::timing::Timings;
use std::{
    fmt,
    sync::atomic::{AtomicU64, Ordering},
};
use z3::{
    Params, SatResult, Solver,
    ast::{Ast, Bool, Datatype},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SearchLimits {
    /// Maximum distinct reachable non-leaf proof values. Shared subproofs count once.
    pub max_rule_slots: usize,
    /// Maximum premises at an inference; list cells do not consume slots.
    pub max_premises: usize,
    /// Maximum operands of any encoded Plus, Times, And, or Or at every depth.
    pub max_finop_arity: usize,
    /// Maximum true ambient dependency bits at the root; None is unrestricted.
    pub max_root_dependencies: Option<usize>,
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
                "no proof within encoding and budget ({} rule slots, {} premises, finop arity {}, root dependencies {})",
                l.max_rule_slots,
                l.max_premises,
                l.max_finop_arity,
                l.max_root_dependencies
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "unbounded".into())
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
    Assumption(AssumptionRef),
    Established(u64),
}
struct Leaf {
    value: Datatype,
    source: Source,
    premise: Option<Premise>,
    dependencies: BTreeSet<usize>,
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
    ambient: Vec<AssumptionId>,
    assumption_formulas: Vec<Datatype>,
    slots: Vec<Datatype>,
    dependencies: Vec<Vec<Bool>>,
    root_dependencies: Vec<Bool>,
}
impl<'a> Query<'a> {
    fn new(
        context: &'a ProofContext,
        conclusion: &Expr<()>,
        interpreter: &impl FormulaInterpreter,
        limits: SearchLimits,
    ) -> Result<Self, SearchError> {
        // Codecs have independent intern tables, so each search needs its own
        // namespace in the shared thread-local Z3 context. IDs are not rendered.
        static NEXT_QUERY: AtomicU64 = AtomicU64::new(0);
        let id = NEXT_QUERY.fetch_add(1, Ordering::Relaxed);
        let namespace = format!("nd_search_{id}");
        Self::build(context, conclusion, interpreter, limits, &namespace)
    }
    fn build(
        context: &'a ProofContext,
        conclusion: &Expr<()>,
        interpreter: &impl FormulaInterpreter,
        limits: SearchLimits,
        namespace: &str,
    ) -> Result<Self, SearchError> {
        if limits.timeout_ms == Some(0) {
            return Err(SearchError::InvalidOptions(
                "zero timeout means unlimited in Z3; use None",
            ));
        }
        let checked = interpreter
            .check(context, conclusion)
            .map_err(SearchError::InvalidConclusion)?;
        let mut expressions = ExprDatatype::with_max_finop_arity(
            &format!("{namespace}.expr"),
            limits.max_finop_arity,
        );
        // Generated predicates may use any existing parameter, including names
        // absent from the requested conclusion and currently established facts.
        let mut parameters = context.types.types.keys().cloned().collect::<Vec<_>>();
        parameters.sort();
        for variable in parameters {
            expressions.encode(&Expr::<()>::new(RawExpr::Variable(variable)))?;
        }
        let proofs = ProofDatatype::new(&format!("{namespace}.proof"), &expressions);
        let target = expressions.encode(&checked.meaning())?;
        let ambient = context.assumptions.keys().copied().collect::<Vec<_>>();
        let indices = ambient
            .iter()
            .enumerate()
            .map(|(i, id)| (*id, i))
            .collect::<BTreeMap<_, _>>();
        let occupied = context.types.types.keys().cloned().collect();
        let mut assumption_formulas = Vec::new();
        for id in &ambient {
            let formula: Expr<()> = crate::type_resolver::avoid_bound_collisions(
                context.assumptions[id].formula.analyzed(),
                &occupied,
            )
            .with_default_metadata();
            assumption_formulas.push(expressions.encode(&formula)?);
        }
        let mut leaves = Vec::new();
        for fact in context.facts() {
            for derivation in fact.derivations() {
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
                    .expect("checked contextual source")
                    .with_default_metadata();
                let formula = expressions.encode(&meaning)?;
                let source = if let Some(id) = premise.assumption {
                    Source::Assumption(AssumptionRef::Ambient(indices[&id] as u64))
                } else {
                    Source::Established(leaves.len() as u64)
                };
                let value = match source {
                    Source::Assumption(a) => proofs.assumption(&formula, a, &expressions)?,
                    Source::Established(i) => proofs.established(&formula, i, &expressions)?,
                };
                leaves.push(Leaf {
                    value,
                    source,
                    premise: Some(premise),
                    dependencies: derivation
                        .assumptions
                        .iter()
                        .map(|id| indices[id])
                        .collect(),
                });
            }
        }
        for i in 0..limits.max_rule_slots {
            let formula = expressions.constant(format!("{namespace}.temporary_formula_{i}"));
            assumption_formulas.push(formula.clone());
            let source = AssumptionRef::Temporary(i as u64);
            leaves.push(Leaf {
                value: proofs.assumption(&formula, source, &expressions)?,
                source: Source::Assumption(source),
                premise: None,
                dependencies: BTreeSet::from([ambient.len() + i]),
            });
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
        // Assert the ground target first. Besides constraining search immediately,
        // this lets Z3's benchmark printer declare the expression datatypes before
        // the proof datatypes that refer to them.
        solver.assert(target.eq(proofs.conclusion(&root)?));
        solver.assert(proofs.bounded_structure(
            &root,
            &slots,
            &leaf_values,
            limits.max_premises,
        )?);
        solver.assert(proofs.rule_constraints(&expressions, &slots, limits.max_premises)?);
        let dependencies = slots
            .iter()
            .map(|_| {
                assumption_formulas
                    .iter()
                    .map(|_| Bool::fresh_const("proof_depends"))
                    .collect()
            })
            .collect();
        let root_dependencies = assumption_formulas
            .iter()
            .map(|_| Bool::fresh_const("root_depends"))
            .collect();
        let query = Self {
            context,
            checked,
            limits,
            expressions,
            proofs,
            solver,
            root,
            target,
            leaves,
            ambient,
            assumption_formulas,
            slots,
            dependencies,
            root_dependencies,
        };
        query.solver.assert(query.dependency_constraints()?);
        Ok(query)
    }
    fn dependency(&self, value: &Datatype, assumption: usize) -> Result<Bool, SearchError> {
        let mut choices = self
            .leaves
            .iter()
            .filter(|l| l.dependencies.contains(&assumption))
            .map(|l| value.eq(&l.value))
            .collect::<Vec<_>>();
        for (slot, bits) in self.slots.iter().zip(&self.dependencies) {
            choices.push(Bool::and(&[
                value.eq(slot),
                self.proofs.is_inference(slot)?,
                bits[assumption].clone(),
            ]));
        }
        Ok(Bool::or(&choices))
    }
    fn dependency_constraints(&self) -> Result<Bool, SearchError> {
        let mut constraints = Vec::new();
        for (i, slot) in self.slots.iter().enumerate() {
            for bit in &self.dependencies[i] {
                constraints.push(self.proofs.is_unused(slot)?.implies(bit.not()));
            }
            for (shape, premises) in self.proofs.premise_cases(slot, self.limits.max_premises)? {
                let and_case = Bool::and(&[
                    shape.clone(),
                    self.proofs
                        .and_introduction(&self.expressions, &premises, slot)?,
                ]);
                for a in 0..self.assumption_formulas.len() {
                    let child_bits = premises
                        .iter()
                        .map(|p| self.dependency(p, a))
                        .collect::<Result<Vec<_>, _>>()?;
                    constraints
                        .push(and_case.implies(self.dependencies[i][a].eq(Bool::or(&child_bits))));
                }
                if premises.len() == 1 {
                    let elimination_case = Bool::and(&[
                        shape.clone(),
                        self.proofs
                            .and_elimination(&self.expressions, &premises[0], slot)?,
                    ]);
                    for a in 0..self.assumption_formulas.len() {
                        constraints.push(elimination_case.implies(
                            self.dependencies[i][a].eq(self.dependency(&premises[0], a)?),
                        ));
                    }
                    let implication_case = Bool::and(&[
                        shape,
                        self.proofs.implication_introduction(
                            &self.expressions,
                            &premises[0],
                            slot,
                        )?,
                    ]);
                    let antecedent = self
                        .expressions
                        .antecedent(&self.proofs.conclusion(slot)?)?;
                    for (a, formula) in self.assumption_formulas.iter().enumerate() {
                        let bit = Bool::and(&[
                            self.dependency(&premises[0], a)?,
                            formula.eq(&antecedent).not(),
                        ]);
                        constraints.push(implication_case.implies(self.dependencies[i][a].eq(bit)));
                    }
                }
            }
        }
        for (a, bit) in self.root_dependencies.iter().enumerate() {
            constraints.push(bit.eq(self.dependency(&self.root, a)?));
            if a >= self.ambient.len() {
                constraints.push(bit.not());
            }
        }
        if let Some(bound) = self.limits.max_root_dependencies {
            constraints.push(at_most(
                &self.root_dependencies[..self.ambient.len()],
                bound,
            ));
        }
        Ok(Bool::and(&constraints))
    }
    fn decode(&self, model: &z3::Model) -> Result<Derivation, SearchError> {
        for assertion in self.solver.get_assertions() {
            if model.eval(&assertion, true).and_then(|b| b.as_bool()) != Some(true) {
                return Err(SearchError::InvalidModel(
                    "model does not satisfy proof query".into(),
                ));
            }
        }
        let mut decoder = Decoder::new(self, model)?;
        let root = decoder.evaluate(&self.root)?;
        if self.proofs.conclusion(&root)?.simplify() != self.target {
            return Err(SearchError::InvalidModel(
                "root conclusion differs from requested formula".into(),
            ));
        }
        let (input, dependencies) = decoder.decode_value(&root, self.limits.max_rule_slots)?;
        let model_dependencies = decoder.read_bits(&self.root_dependencies)?;
        if dependencies != model_dependencies
            || dependencies.iter().any(|a| *a >= self.ambient.len())
        {
            return Err(SearchError::InvalidModel(
                "root dependency mismatch or escaping temporary assumption".into(),
            ));
        }
        if self
            .limits
            .max_root_dependencies
            .is_some_and(|bound| dependencies.len() > bound)
        {
            return Err(SearchError::InvalidModel(
                "root dependency bound exceeded".into(),
            ));
        }
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
        derivation.assumptions = model_dependencies
            .iter()
            .map(|a| self.ambient[*a])
            .collect();
        self.context
            .refresh_scopes(&mut derivation, self.checked.free_variables());
        Ok(derivation)
    }
}

struct Decoder<'a, 'c> {
    query: &'a Query<'c>,
    model: &'a z3::Model,
    temporary_ids: BTreeMap<usize, AssumptionId>,
    slot_values: Vec<Datatype>,
}
impl<'a, 'c> Decoder<'a, 'c> {
    fn new(query: &'a Query<'c>, model: &'a z3::Model) -> Result<Self, SearchError> {
        let slot_values = query
            .slots
            .iter()
            .map(|v| {
                model
                    .eval(v, true)
                    .ok_or_else(|| SearchError::InvalidModel("slot was not evaluated".into()))
            })
            .collect::<Result<_, _>>()?;
        Ok(Self {
            query,
            model,
            temporary_ids: BTreeMap::new(),
            slot_values,
        })
    }
    fn evaluate(&self, value: &Datatype) -> Result<Datatype, SearchError> {
        self.model
            .eval(value, true)
            .ok_or_else(|| SearchError::InvalidModel("term was not evaluated".into()))
    }
    fn read_bits(&self, bits: &[Bool]) -> Result<BTreeSet<usize>, SearchError> {
        let mut set = BTreeSet::new();
        for (a, bit) in bits.iter().enumerate() {
            match self.model.eval(bit, true).and_then(|b| b.as_bool()) {
                Some(true) => {
                    set.insert(a);
                }
                Some(false) => (),
                None => {
                    return Err(SearchError::InvalidModel(
                        "dependency bit was not evaluated".into(),
                    ));
                }
            }
        }
        Ok(set)
    }
    fn assumption_id(&mut self, index: usize) -> AssumptionId {
        if index < self.query.ambient.len() {
            self.query.ambient[index]
        } else {
            *self
                .temporary_ids
                .entry(index)
                .or_insert_with(|| AssumptionId(super::context::fresh()))
        }
    }
    fn decode_value(
        &mut self,
        value: &Datatype,
        remaining: usize,
    ) -> Result<(ProofInput, BTreeSet<usize>), SearchError> {
        let node = self
            .query
            .proofs
            .inspect(value, &self.query.expressions)
            .map_err(model_error)?;
        let (formula, source) = match node {
            ProofNode::Unused => return Err(SearchError::InvalidModel("unused proof node".into())),
            ProofNode::Assumption { conclusion, source } => {
                (conclusion, Source::Assumption(source))
            }
            ProofNode::Established { conclusion, source } => {
                (conclusion, Source::Established(source))
            }
            ProofNode::Inference {
                conclusion,
                rule,
                premises,
            } => {
                if remaining == 0 {
                    return Err(SearchError::InvalidModel(
                        "inference depth exceeds slot budget".into(),
                    ));
                }
                let children = self
                    .query
                    .proofs
                    .read_premises(&premises, self.query.limits.max_premises)
                    .map_err(model_error)?;
                if children.is_empty() {
                    return Err(SearchError::InvalidModel("empty inference".into()));
                }
                let mut inputs = Vec::new();
                let mut child_sets = Vec::new();
                for child in children {
                    let (input, set) = self.decode_value(&child, remaining - 1)?;
                    inputs.push(input);
                    child_sets.push(set);
                }
                let meaning = self
                    .query
                    .expressions
                    .decode(&conclusion)
                    .map_err(model_error)?;
                self.query.context.check(&meaning).map_err(|e| {
                    SearchError::InvalidModel(format!("ill-typed inference conclusion: {e}"))
                })?;
                let mut dependencies = child_sets
                    .iter()
                    .flat_map(|s| s.iter().copied())
                    .collect::<BTreeSet<_>>();
                let proof = match rule {
                    ProofRule::AndIntroduction => {
                        if meaning
                            != Expr::new(RawExpr::Finop(
                                Finop::And,
                                inputs.iter().map(|p| p.conclusion().clone()).collect(),
                            ))
                        {
                            return Err(SearchError::InvalidModel(
                                "conjunction conclusion differs from premises".into(),
                            ));
                        }
                        NaturalDeductionProof::ConjunctionIntroduction { premises: inputs }
                    }
                    ProofRule::AndElimination => {
                        if inputs.len() != 1 {
                            return Err(SearchError::InvalidModel(
                                "conjunction elimination requires one premise".into(),
                            ));
                        }
                        let RawExpr::Finop(Finop::And, operands) = &inputs[0].conclusion().raw
                        else {
                            return Err(SearchError::InvalidModel(
                                "conjunction premise expected".into(),
                            ));
                        };
                        let operand =
                            operands.iter().position(|p| p == &meaning).ok_or_else(|| {
                                SearchError::InvalidModel(
                                    "conclusion is not an immediate conjunct".into(),
                                )
                            })?;
                        NaturalDeductionProof::ConjunctionElimination {
                            premise: inputs.remove(0),
                            operand,
                        }
                    }
                    ProofRule::ImplicationIntroduction => {
                        if inputs.len() != 1 {
                            return Err(SearchError::InvalidModel(
                                "implication introduction requires one premise".into(),
                            ));
                        }
                        let RawExpr::LogicChain(chain) = &meaning.raw else {
                            return Err(SearchError::InvalidModel(
                                "implication conclusion expected".into(),
                            ));
                        };
                        let [(Logic::Imp, body)] = chain.assertions.as_slice() else {
                            return Err(SearchError::InvalidModel(
                                "single implication expected".into(),
                            ));
                        };
                        if body != inputs[0].conclusion() {
                            return Err(SearchError::InvalidModel(
                                "implication consequent differs from premise".into(),
                            ));
                        }
                        let mut discharged = BTreeSet::new();
                        let mut discharged_formulas = BTreeMap::new();
                        let antecedent = self.query.expressions.antecedent(&conclusion)?;
                        for a in dependencies.clone() {
                            let formula = self.evaluate(&self.query.assumption_formulas[a])?;
                            if formula == antecedent.simplify() {
                                dependencies.remove(&a);
                                let id = self.assumption_id(a);
                                discharged.insert(id);
                                discharged_formulas.insert(
                                    id,
                                    self.query
                                        .expressions
                                        .decode(&formula)
                                        .map_err(model_error)?,
                                );
                            }
                        }
                        NaturalDeductionProof::ImplicationIntroduction {
                            premise: inputs.remove(0),
                            discharged,
                            discharged_formulas,
                        }
                    }
                };
                let slot = self
                    .slot_values
                    .iter()
                    .position(|v| v == value)
                    .ok_or_else(|| {
                        SearchError::InvalidModel("inference has no active slot".into())
                    })?;
                if self.read_bits(&self.query.dependencies[slot])? != dependencies {
                    return Err(SearchError::InvalidModel(
                        "inference dependency mismatch".into(),
                    ));
                }
                return Ok((ProofInput::local(meaning, proof), dependencies));
            }
        };
        let leaf = self
            .query
            .leaves
            .iter()
            .find(|l| l.source == source)
            .ok_or_else(|| SearchError::InvalidModel("unknown leaf source".into()))?;
        if self.evaluate(&leaf.value)? != *value {
            return Err(SearchError::InvalidModel(
                "leaf formula differs from registered source".into(),
            ));
        }
        let meaning = self
            .query
            .expressions
            .decode(&formula)
            .map_err(model_error)?;
        let dependencies = leaf.dependencies.clone();
        let input = if let Some(premise) = &leaf.premise {
            let mut input = super::proof::view_input(self.query.context, premise);
            if input.conclusion() != &meaning {
                input = ProofInput::local(
                    meaning,
                    NaturalDeductionProof::Reuse {
                        premise: input,
                        kind: ReuseKind::Resolved,
                    },
                );
            }
            input
        } else {
            self.query.context.check(&meaning).map_err(|e| {
                SearchError::InvalidModel(format!("invalid temporary formula: {e}"))
            })?;
            let id = self.assumption_id(*dependencies.iter().next().unwrap());
            ProofInput::local(
                meaning,
                NaturalDeductionProof::Assumption { assumption: id },
            )
        };
        Ok((input, dependencies))
    }
}

/// Find one proof without changing the context. Accepted facts are leaves,
/// irrespective of how they were established. Temporary assumptions must be
/// discharged at the root. Returned dependencies are the exact model set, before
/// recording-time witness-discharge alternatives. The caller explicitly records it.
pub fn find_proof(
    context: &ProofContext,
    conclusion: &Expr<()>,
    interpreter: &impl FormulaInterpreter,
    limits: SearchLimits,
    timings: &Timings,
) -> Result<(CheckedFormula, Derivation), SearchError> {
    let _total = timings.scope("total_ms");
    let query = {
        let _query = timings.scope("query_ms");
        Query::new(context, conclusion, interpreter, limits)?
    };
    let status = timings.check(&query.solver, "z3_dt_ms");
    let reason = if status == SatResult::Unknown {
        query.solver.get_reason_unknown()
    } else {
        None
    };
    check_status(status, reason, limits)?;
    let _decode = timings.scope("decode_ms");
    let model = query
        .solver
        .get_model()
        .ok_or_else(|| SearchError::InvalidModel("satisfiable query has no model".into()))?;
    let derivation = query.decode(&model)?;
    Ok((query.checked, derivation))
}

#[cfg(test)]
mod tests;
