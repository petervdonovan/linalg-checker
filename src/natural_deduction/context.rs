use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_ID: AtomicU64 = AtomicU64::new(1);
fn fresh() -> u64 {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

macro_rules! identity {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u64);
    };
}
identity!(ScopeId);
identity!(AssumptionId);
identity!(FactId);
identity!(DerivationId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assumption {
    pub id: AssumptionId,
    pub scope: ScopeId,
    pub expression: Expr<()>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    pub scope: ScopeId,
    pub ty: TypeExpr<()>,
    pub witness: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessScope {
    pub scope: ScopeId,
    pub assumption: AssumptionId,
    pub variables: BTreeSet<Variable>,
    pub source: DerivationId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessDischarge {
    pub assumption: AssumptionId,
    pub source: DerivationId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub id: DerivationId,
    pub assumptions: BTreeSet<AssumptionId>,
    pub required_variables: BTreeSet<Variable>,
    pub required_scopes: BTreeSet<ScopeId>,
    pub proof: NaturalDeductionProof,
    pub witness_discharges: Vec<WitnessDischarge>,
    pub side_condition_premises: Vec<DerivationId>,
}
impl Derivation {
    pub(crate) fn new(proof: NaturalDeductionProof) -> Self {
        Self {
            id: DerivationId(0),
            assumptions: BTreeSet::new(),
            required_variables: BTreeSet::new(),
            required_scopes: BTreeSet::new(),
            proof,
            witness_discharges: Vec::new(),
            side_condition_premises: Vec::new(),
        }
    }
    pub(crate) fn dominates(&self, other: &Self) -> bool {
        self.assumptions.is_subset(&other.assumptions)
            && self.required_variables.is_subset(&other.required_variables)
            && self.required_scopes.is_subset(&other.required_scopes)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fact {
    pub id: FactId,
    pub expression: Expr<()>,
    /// Alternative representations are supplied by the trusted elaborator.
    pub alternatives: Vec<Expr<()>>,
    pub analyzed: Option<Expr<crate::type_resolver::TypedMetadata>>,
    pub alternative_analyses: Vec<Option<Expr<crate::type_resolver::TypedMetadata>>>,
    pub derivations: Vec<Derivation>,
}

/// Cloning a context opens an isolated branch. IDs remain unique across branches.
#[derive(Clone, Debug)]
pub struct ProofContext {
    pub types: SymbolicTypeEnvironment,
    pub(crate) facts: Vec<Fact>,
    pub(crate) assumptions: BTreeMap<AssumptionId, Assumption>,
    pub(crate) parameters: BTreeMap<Variable, Parameter>,
    pub(crate) witnesses: Vec<WitnessScope>,
    pub(crate) scopes: BTreeSet<ScopeId>,
    pub(crate) current_scope: ScopeId,
    // Keep superseded derivations for provenance references.
    pub(crate) archive: BTreeMap<DerivationId, Derivation>,
}
impl Default for ProofContext {
    fn default() -> Self {
        let scope = ScopeId(fresh());
        Self {
            types: SymbolicTypeEnvironment::default(),
            facts: Vec::new(),
            assumptions: BTreeMap::new(),
            parameters: BTreeMap::new(),
            witnesses: Vec::new(),
            scopes: BTreeSet::from([scope]),
            current_scope: scope,
            archive: BTreeMap::new(),
        }
    }
}
impl ProofContext {
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }
    pub fn assumptions(&self) -> &BTreeMap<AssumptionId, Assumption> {
        &self.assumptions
    }
    pub fn derivation(&self, id: DerivationId) -> Option<&Derivation> {
        self.archive.get(&id)
    }
    pub fn enter_scope(&mut self) -> ScopeId {
        let id = ScopeId(fresh());
        self.scopes.insert(id);
        self.current_scope = id;
        id
    }
    pub fn declare_parameter(&mut self, variable: Variable, ty: TypeExpr<()>) {
        self.types.types.insert(variable.clone(), ty.clone());
        self.parameters.entry(variable).or_insert(Parameter {
            scope: self.current_scope,
            ty,
            witness: false,
        });
    }
    pub fn assume(&mut self, expression: Expr<()>, alternatives: Vec<Expr<()>>) -> AssumptionId {
        let id = AssumptionId(fresh());
        self.assumptions.insert(
            id,
            Assumption {
                id,
                scope: self.current_scope,
                expression: expression.clone(),
            },
        );
        let mut derivation = Derivation::new(NaturalDeductionProof::Assumption { assumption: id });
        derivation.assumptions.insert(id);
        self.record(expression, alternatives, vec![derivation]);
        id
    }
    /// Conservative adapter for existing solver/tactic validation.
    pub fn record_external(&mut self, expression: Expr<()>, alternatives: Vec<Expr<()>>) {
        self.record_external_with_proof(expression, alternatives, NaturalDeductionProof::External);
    }
    pub(crate) fn record_external_with_proof(
        &mut self,
        expression: Expr<()>,
        alternatives: Vec<Expr<()>>,
        proof: NaturalDeductionProof,
    ) {
        let mut derivation = Derivation::new(proof);
        derivation
            .assumptions
            .extend(self.assumptions.keys().copied());
        derivation
            .required_variables
            .extend(self.parameters.keys().cloned());
        self.record(expression, alternatives, vec![derivation]);
    }
    pub(crate) fn free_variables<'a>(
        &self,
        expressions: impl Iterator<Item = &'a Expr<()>>,
    ) -> BTreeSet<Variable> {
        let mut variables = BTreeSet::new();
        for e in expressions {
            if let Some(fact) = self.facts.iter().find(|f| f.expression == *e)
                && let Some(analysis) = &fact.analyzed
                && let Some(free) = &analysis.meta.free_variables
            {
                variables.extend(free.iter().cloned());
                continue;
            }
            variables.extend(crate::formula::free_variables_in_context(
                std::iter::once(e),
                &self.types.types.keys().cloned().collect(),
            ));
        }
        variables
    }
    pub(crate) fn analyzed_view(
        &self,
        premise: &Premise,
    ) -> Option<Expr<crate::type_resolver::TypedMetadata>> {
        let fact = self.facts.iter().find(|f| f.id == premise.fact)?;
        let analyzed = match premise.alternative {
            Some(i) => fact.alternative_analyses.get(i)?.as_ref()?,
            None => fact.analyzed.as_ref()?,
        };
        let normalized = crate::type_resolver::avoid_bound_collisions(
            analyzed,
            &self.types.types.keys().cloned().collect(),
        );
        conjunction_views(&normalized)
            .get(premise.conjunct)
            .map(|e| (*e).clone())
    }
    pub(crate) fn variables_with_types(
        &self,
        mut variables: BTreeSet<Variable>,
    ) -> BTreeSet<Variable> {
        loop {
            let before = variables.len();
            for variable in variables.clone() {
                if let Some(ty) = self.types.types.get(&variable) {
                    variables.extend(
                        self.free_variables(std::iter::once(&Expr::new(RawExpr::Type(ty.clone())))),
                    );
                }
            }
            if before == variables.len() {
                return variables;
            }
        }
    }
    pub(crate) fn dependency_variables(
        &self,
        assumptions: &BTreeSet<AssumptionId>,
    ) -> BTreeSet<Variable> {
        self.variables_with_types(
            self.free_variables(
                assumptions
                    .iter()
                    .filter_map(|id| self.assumptions.get(id).map(|a| &a.expression)),
            ),
        )
    }
    pub(crate) fn refresh_scopes(&self, derivation: &mut Derivation, expression: &Expr<()>) {
        derivation
            .required_variables
            .extend(self.free_variables(std::iter::once(expression)));
        derivation
            .required_variables
            .extend(self.dependency_variables(&derivation.assumptions));
        derivation.required_variables =
            self.variables_with_types(derivation.required_variables.clone());
        derivation.required_scopes = derivation
            .required_variables
            .iter()
            .filter_map(|v| self.parameters.get(v).map(|p| p.scope))
            .collect();
    }
    pub(crate) fn discharge_witnesses(
        &self,
        expression: &Expr<()>,
        original: &Derivation,
    ) -> Derivation {
        let mut result = original.clone();
        loop {
            let mut changed = false;
            for witness in self.witnesses.iter().rev() {
                if !result.assumptions.contains(&witness.assumption) {
                    continue;
                }
                let mut remaining = result.assumptions.clone();
                remaining.remove(&witness.assumption);
                let mut free = self.dependency_variables(&remaining);
                free.extend(
                    self.variables_with_types(self.free_variables(std::iter::once(expression))),
                );
                if !free.is_disjoint(&witness.variables) {
                    continue;
                }
                let Some(source) = self.derivation(witness.source) else {
                    continue;
                };
                result.assumptions = remaining;
                result.assumptions.extend(&source.assumptions);
                result
                    .required_variables
                    .retain(|v| !witness.variables.contains(v));
                result
                    .required_variables
                    .extend(source.required_variables.iter().cloned());
                result.witness_discharges.push(WitnessDischarge {
                    assumption: witness.assumption,
                    source: witness.source,
                });
                self.refresh_scopes(&mut result, expression);
                changed = true;
            }
            if !changed {
                return result;
            }
        }
    }
    /// Commit the witness source explicitly selected by the caller.
    pub fn open_witness(
        &mut self,
        expression: Expr<()>,
        alternatives: Vec<Expr<()>>,
        source: Derivation,
    ) {
        assert!(matches!(
            source.proof,
            NaturalDeductionProof::ExistentialElimination { .. }
        ));
        self.record(expression, alternatives, vec![source]);
    }
    /// Accept checked derivations. Witness opening creates a local assumption;
    /// other results undergo automatic, side-condition-checked witness discharge.
    pub fn record(
        &mut self,
        expression: Expr<()>,
        alternatives: Vec<Expr<()>>,
        derivations: Vec<Derivation>,
    ) {
        let mut accepted = Vec::new();
        let derivation_count = derivations.len();
        for mut derivation in derivations {
            if let NaturalDeductionProof::ExistentialElimination {
                source,
                assignments,
                introduced_types,
                ..
            } = &derivation.proof
            {
                assert_eq!(
                    derivation_count, 1,
                    "select one witness source before accepting an opening"
                );
                let scope = ScopeId(fresh());
                self.scopes.insert(scope);
                let assumption = AssumptionId(fresh());
                let variables = assignments.values().cloned().collect::<BTreeSet<_>>();
                for (variable, ty) in introduced_types {
                    self.types.types.insert(variable.clone(), ty.clone());
                    self.parameters.insert(
                        variable.clone(),
                        Parameter {
                            scope,
                            ty: ty.clone(),
                            witness: true,
                        },
                    );
                }
                self.assumptions.insert(
                    assumption,
                    Assumption {
                        id: assumption,
                        scope,
                        expression: expression.clone(),
                    },
                );
                self.witnesses.push(WitnessScope {
                    scope,
                    assumption,
                    variables,
                    source: source.derivation,
                });
                derivation.assumptions.insert(assumption);
            }
            self.refresh_scopes(&mut derivation, &expression);
            let discharged = self.discharge_witnesses(&expression, &derivation);
            accepted.push(derivation);
            accepted.push(discharged);
        }
        let index = self
            .facts
            .iter()
            .position(|f| f.expression == expression)
            .unwrap_or_else(|| {
                self.facts.push(Fact {
                    id: FactId(fresh()),
                    expression: expression.clone(),
                    alternatives: Vec::new(),
                    analyzed: crate::type_resolver::analyze_formula(&self.types, &expression).ok(),
                    alternative_analyses: Vec::new(),
                    derivations: Vec::new(),
                });
                self.facts.len() - 1
            });
        for alternative in alternatives {
            if !self.facts[index].alternatives.contains(&alternative) {
                let analyzed =
                    crate::type_resolver::analyze_formula(&self.types, &alternative).ok();
                self.facts[index].alternative_analyses.push(analyzed);
                self.facts[index].alternatives.push(alternative);
            }
        }
        for mut derivation in accepted {
            if self.facts[index]
                .derivations
                .iter()
                .any(|d| d.dominates(&derivation))
            {
                continue;
            }
            derivation.id = DerivationId(fresh());
            self.archive.insert(derivation.id, derivation.clone());
            self.facts[index]
                .derivations
                .retain(|d| !derivation.dominates(d));
            self.facts[index].derivations.push(derivation);
        }
    }
    pub fn exportable_to(&self, parent: &Self) -> Vec<Fact> {
        self.facts
            .iter()
            .filter_map(|fact| {
                let mut fact = fact.clone();
                fact.derivations.retain(|d| {
                    d.assumptions
                        .iter()
                        .all(|a| parent.assumptions.contains_key(a))
                        && d.required_scopes.is_subset(&parent.scopes)
                        && self
                            .variables_with_types(
                                self.free_variables(std::iter::once(&fact.expression)),
                            )
                            .iter()
                            .all(|v| parent.parameters.contains_key(v))
                });
                (!fact.derivations.is_empty()).then_some(fact)
            })
            .collect()
    }
    /// Import a certificate whose environment coverage was checked by the caller.
    pub(crate) fn import(&mut self, fact: Fact, archive: &BTreeMap<DerivationId, Derivation>) {
        self.archive.extend(archive.clone());
        let identity = fact.id;
        let expression = fact.expression.clone();
        let analyzed = fact.analyzed.clone();
        let alternative_analyses = fact.alternative_analyses.clone();
        let new = !self.facts.iter().any(|f| f.expression == expression);
        self.record(fact.expression, fact.alternatives, fact.derivations);
        if new && let Some(imported) = self.facts.iter_mut().find(|f| f.expression == expression) {
            imported.id = identity;
            imported.analyzed = analyzed;
            imported.alternative_analyses = alternative_analyses;
        }
    }
}
