use super::*;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_ID: AtomicU64 = AtomicU64::new(1);
pub(super) fn fresh() -> u64 {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

macro_rules! identity {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u64);
    };
}
identity!(StoreId);
identity!(InterpretationId);
identity!(ScopeId);
identity!(AssumptionId);
identity!(FactId);
identity!(DerivationId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assumption {
    pub id: AssumptionId,
    pub scope: ScopeId,
    pub expression: Expr<()>,
    pub(crate) formula: CheckedFormula,
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
pub struct FactContent {
    pub(crate) id: FactId,
    pub(crate) expression: Expr<()>,
    pub(crate) formula: CheckedFormula,
    pub(crate) alternatives: Vec<CheckedFormula>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fact {
    content: Rc<FactContent>,
    pub(crate) derivations: Vec<Rc<Derivation>>,
}
impl std::ops::Deref for Fact {
    type Target = FactContent;
    fn deref(&self) -> &FactContent {
        &self.content
    }
}
impl Fact {
    pub fn id(&self) -> FactId {
        self.id
    }
    pub fn formula(&self) -> &CheckedFormula {
        &self.formula
    }
    pub fn derivations(&self) -> impl Iterator<Item = &Derivation> {
        self.derivations.iter().map(Rc::as_ref)
    }
}
#[derive(Debug)]
pub struct ProofStore {
    id: StoreId,
    facts: BTreeMap<FactId, Rc<FactContent>>,
    derivations: BTreeMap<DerivationId, Rc<Derivation>>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContextError {
    ForeignStore,
    UnknownProof(DerivationId),
    UnknownFact(FactId),
    InaccessibleProof(DerivationId),
    StaleBinding(Variable),
    InvalidWitness,
    EmptyProof,
}
impl std::fmt::Display for ContextError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid proof-context operation: {self:?}")
    }
}
impl std::error::Error for ContextError {}
#[derive(Debug)]
pub struct ExportDelta {
    store: StoreId,
    facts: Vec<Fact>,
}
impl ExportDelta {
    pub fn len(&self) -> usize {
        self.facts.len()
    }
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}
#[derive(Clone, Debug)]
pub struct ProofContext {
    pub(crate) types: SymbolicTypeEnvironment,
    pub(crate) facts: Vec<Fact>,
    pub(crate) assumptions: BTreeMap<AssumptionId, Assumption>,
    pub(crate) parameters: BTreeMap<Variable, Parameter>,
    pub(crate) witnesses: Vec<WitnessScope>,
    pub(crate) scopes: BTreeSet<ScopeId>,
    pub(crate) current_scope: ScopeId,
    store: Rc<std::cell::RefCell<ProofStore>>,
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
            store: Rc::new(std::cell::RefCell::new(ProofStore {
                id: StoreId(fresh()),
                facts: BTreeMap::new(),
                derivations: BTreeMap::new(),
            })),
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
    pub fn derivation(&self, id: DerivationId) -> Option<Rc<Derivation>> {
        self.store.borrow().derivations.get(&id).cloned()
    }
    pub fn types(&self) -> &SymbolicTypeEnvironment {
        &self.types
    }
    pub fn store_id(&self) -> StoreId {
        self.store.borrow().id
    }
    pub fn shares_store_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.store, &other.store)
    }
    pub fn store_counts(&self) -> (usize, usize) {
        let store = self.store.borrow();
        (store.facts.len(), store.derivations.len())
    }
    pub fn check(
        &self,
        expression: &Expr<()>,
    ) -> Result<CheckedFormula, crate::type_resolver::TypeError> {
        CheckedFormula::from_interpreted(self, expression, expression.clone())
    }

    pub fn enter_scope(&mut self) -> ScopeId {
        let id = ScopeId(fresh());
        self.scopes.insert(id);
        self.current_scope = id;
        id
    }
    pub fn declare_parameter(&mut self, variable: Variable, ty: TypeExpr<()>) {
        if let Some(existing) = self.parameters.get(&variable) {
            assert_eq!(
                existing.ty, ty,
                "a declaration cannot change a parameter's type"
            );
            return;
        }
        self.types.types.insert(variable.clone(), ty.clone());
        self.parameters.entry(variable).or_insert(Parameter {
            scope: self.current_scope,
            ty,
            witness: false,
        });
    }
    pub fn assume(
        &mut self,
        formula: CheckedFormula,
        alternatives: Vec<CheckedFormula>,
    ) -> Result<AssumptionId, ContextError> {
        self.validate_formula(&formula, &BTreeMap::new())?;
        for view in &alternatives {
            self.validate_formula(view, &BTreeMap::new())?;
        }
        let id = AssumptionId(fresh());
        self.assumptions.insert(
            id,
            Assumption {
                id,
                scope: self.current_scope,
                expression: formula.meaning(),
                formula: formula.clone(),
            },
        );
        let mut d = Derivation::new(NaturalDeductionProof::Assumption { assumption: id });
        d.assumptions.insert(id);
        self.record(formula, alternatives, vec![d])?;
        Ok(id)
    }
    pub fn record_external(
        &mut self,
        formula: CheckedFormula,
        alternatives: Vec<CheckedFormula>,
    ) -> Result<FactId, ContextError> {
        self.record_external_with_proof(formula, alternatives, NaturalDeductionProof::External)
    }
    pub(crate) fn record_external_with_proof(
        &mut self,
        formula: CheckedFormula,
        alternatives: Vec<CheckedFormula>,
        proof: NaturalDeductionProof,
    ) -> Result<FactId, ContextError> {
        let mut d = Derivation::new(proof);
        d.assumptions.extend(self.assumptions.keys().copied());
        d.required_variables.extend(self.parameters.keys().cloned());
        self.record(formula, alternatives, vec![d])
    }
    fn validate_formula(
        &self,
        formula: &CheckedFormula,
        introduced: &BTreeMap<Variable, TypeExpr<()>>,
    ) -> Result<(), ContextError> {
        if formula.store() != self.store_id() {
            return Err(ContextError::ForeignStore);
        }
        for (v, (scope, ty)) in formula.bindings() {
            if let Some(p) = self.parameters.get(v) {
                if p.scope != *scope || p.ty != *ty {
                    return Err(ContextError::StaleBinding(v.clone()));
                }
            } else if introduced.get(v) != Some(ty) {
                return Err(ContextError::StaleBinding(v.clone()));
            }
        }
        Ok(())
    }
    pub(crate) fn analyzed_view(
        &self,
        premise: &Premise,
    ) -> Option<Expr<crate::type_resolver::TypedMetadata>> {
        let fact = self.facts.iter().find(|f| f.id == premise.fact)?;
        let analyzed = match premise.alternative {
            Some(i) => fact.alternatives.get(i)?.analyzed(),
            None => fact.formula.analyzed(),
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
                    variables.extend(free_variables(std::iter::once(&Expr::new(RawExpr::Type(
                        ty.clone(),
                    )))));
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
        let variables = assumptions
            .iter()
            .filter_map(|id| self.assumptions.get(id))
            .flat_map(|a| a.formula.free_variables().iter().cloned())
            .collect();
        self.variables_with_types(variables)
    }

    pub(crate) fn refresh_scopes(&self, derivation: &mut Derivation, free: &BTreeSet<Variable>) {
        derivation.required_variables.extend(free.iter().cloned());
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
        conclusion_free: &BTreeSet<Variable>,
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
                free.extend(self.variables_with_types(conclusion_free.clone()));
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
                self.refresh_scopes(&mut result, conclusion_free);
                changed = true;
            }
            if !changed {
                return result;
            }
        }
    }
    /// Commit exactly the witness source chosen by the caller.
    pub fn open_witness(
        &mut self,
        formula: CheckedFormula,
        alternatives: Vec<CheckedFormula>,
        source: Derivation,
    ) -> Result<FactId, ContextError> {
        if !matches!(
            source.proof,
            NaturalDeductionProof::ExistentialElimination { .. }
        ) {
            return Err(ContextError::InvalidWitness);
        }
        self.record(formula, alternatives, vec![source])
    }
    fn validate_references(&self, d: &Derivation) -> Result<(), ContextError> {
        if d.id != DerivationId(0) && self.derivation(d.id).is_none() {
            return Err(ContextError::UnknownProof(d.id));
        }
        if !d
            .assumptions
            .iter()
            .all(|a| self.assumptions.contains_key(a))
        {
            return Err(ContextError::InaccessibleProof(d.id));
        }
        let premises = match &d.proof {
            NaturalDeductionProof::Reuse { premise, .. }
            | NaturalDeductionProof::UniversalIntroduction { premise, .. }
            | NaturalDeductionProof::ImplicationIntroduction { premise, .. } => vec![premise],
            NaturalDeductionProof::ExistentialIntroduction { premises, .. } => {
                premises.iter().collect()
            }
            NaturalDeductionProof::ExistentialElimination { source, .. } => vec![source],
            NaturalDeductionProof::UniversalElimination {
                source, premises, ..
            } => std::iter::once(source).chain(premises).collect(),
            _ => Vec::new(),
        };
        for p in premises {
            if !self.store.borrow().facts.contains_key(&p.fact) {
                return Err(ContextError::UnknownFact(p.fact));
            }
            if !self
                .facts
                .iter()
                .any(|f| f.id == p.fact && f.derivations.iter().any(|d| d.id == p.derivation))
            {
                return Err(ContextError::InaccessibleProof(p.derivation));
            }
        }
        let mut refs = d.side_condition_premises.clone();
        match &d.proof {
            NaturalDeductionProof::Reuse { premise, .. }
            | NaturalDeductionProof::UniversalIntroduction { premise, .. }
            | NaturalDeductionProof::ImplicationIntroduction { premise, .. } => {
                refs.push(premise.derivation)
            }
            NaturalDeductionProof::ExistentialIntroduction { premises, .. } => {
                refs.extend(premises.iter().map(|p| p.derivation))
            }
            NaturalDeductionProof::ExistentialElimination { source, .. } => {
                refs.push(source.derivation)
            }
            NaturalDeductionProof::UniversalElimination {
                source, premises, ..
            } => {
                refs.push(source.derivation);
                refs.extend(premises.iter().map(|p| p.derivation));
            }
            NaturalDeductionProof::ScopedGoal { cases, .. } => {
                for id in cases {
                    if self.derivation(*id).is_none() {
                        return Err(ContextError::UnknownProof(*id));
                    }
                }
            }
            _ => {}
        }
        for id in refs {
            if self.derivation(id).is_none() {
                return Err(ContextError::UnknownProof(id));
            }
            if !self
                .facts
                .iter()
                .any(|f| f.derivations.iter().any(|d| d.id == id))
            {
                return Err(ContextError::InaccessibleProof(id));
            }
        }
        Ok(())
    }
    pub fn record(
        &mut self,
        formula: CheckedFormula,
        alternatives: Vec<CheckedFormula>,
        derivations: Vec<Derivation>,
    ) -> Result<FactId, ContextError> {
        if derivations.is_empty() {
            return Err(ContextError::EmptyProof);
        }
        let opening = derivations
            .iter()
            .find_map(|d| {
                if let NaturalDeductionProof::ExistentialElimination {
                    introduced_types, ..
                } = &d.proof
                {
                    Some(introduced_types.clone())
                } else {
                    None
                }
            })
            .unwrap_or_default();
        if derivations.iter().any(|d|matches!(&d.proof,NaturalDeductionProof::ExistentialElimination{introduced_types,..} if introduced_types.is_empty())) {return Err(ContextError::InvalidWitness);}
        if !opening.is_empty()
            && (derivations.len() != 1 || opening.keys().any(|v| self.parameters.contains_key(v)))
        {
            return Err(ContextError::InvalidWitness);
        }
        if !opening.is_empty() {
            let NaturalDeductionProof::ExistentialElimination { assignments, .. } =
                &derivations[0].proof
            else {
                return Err(ContextError::InvalidWitness);
            };
            if opening.keys().cloned().collect::<BTreeSet<_>>()
                != assignments.values().cloned().collect()
                || opening.keys().any(|v| !formula.bindings().contains_key(v))
            {
                return Err(ContextError::InvalidWitness);
            }
        }
        self.validate_formula(&formula, &opening)?;
        for view in &alternatives {
            self.validate_formula(view, &opening)?;
        }
        for d in &derivations {
            self.validate_references(d)?;
        }
        let mut accepted = Vec::new();
        for mut d in derivations {
            if let NaturalDeductionProof::ExistentialElimination {
                source,
                assignments,
                introduced_types,
            } = &d.proof
            {
                let assumption = AssumptionId(fresh());
                let mut variables = BTreeSet::new();
                let mut witness_scope = None;
                for (v, ty) in introduced_types {
                    let scope = formula
                        .bindings()
                        .get(v)
                        .ok_or(ContextError::InvalidWitness)?
                        .0;
                    witness_scope = Some(scope);
                    self.scopes.insert(scope);
                    self.types.types.insert(v.clone(), ty.clone());
                    self.parameters.insert(
                        v.clone(),
                        Parameter {
                            scope,
                            ty: ty.clone(),
                            witness: true,
                        },
                    );
                    variables.insert(v.clone());
                }
                let scope = witness_scope.ok_or(ContextError::InvalidWitness)?;
                if variables != assignments.values().cloned().collect() {
                    return Err(ContextError::InvalidWitness);
                }
                self.assumptions.insert(
                    assumption,
                    Assumption {
                        id: assumption,
                        scope,
                        expression: formula.meaning(),
                        formula: formula.clone(),
                    },
                );
                self.witnesses.push(WitnessScope {
                    scope,
                    assumption,
                    variables,
                    source: source.derivation,
                });
                d.assumptions.insert(assumption);
            }
            self.refresh_scopes(&mut d, formula.free_variables());
            let discharged = self.discharge_witnesses(formula.free_variables(), &d);
            accepted.push(d);
            accepted.push(discharged);
        }
        let index = if let Some(i) = self.facts.iter().position(|f| {
            f.formula.same_meaning(&formula)
                && alternatives
                    .iter()
                    .all(|a| f.alternatives.iter().any(|b| a.same_meaning(b)))
        }) {
            i
        } else {
            let id = FactId(fresh());
            let content = Rc::new(FactContent {
                id,
                expression: formula.written().clone(),
                formula,
                alternatives,
            });
            self.store.borrow_mut().facts.insert(id, content.clone());
            self.facts.push(Fact {
                content,
                derivations: Vec::new(),
            });
            self.facts.len() - 1
        };
        for mut d in accepted {
            if self.facts[index]
                .derivations
                .iter()
                .any(|old| old.dominates(&d))
            {
                continue;
            }
            d.id = DerivationId(fresh());
            let d = Rc::new(d);
            self.store.borrow_mut().derivations.insert(d.id, d.clone());
            self.facts[index]
                .derivations
                .retain(|old| !d.dominates(old));
            self.facts[index].derivations.push(d);
        }
        Ok(self.facts[index].id)
    }
    fn export_eligible(&self, fact: &Fact, d: &Derivation, parent: &Self) -> bool {
        d.assumptions
            .iter()
            .all(|a| parent.assumptions.contains_key(a))
            && d.required_scopes.is_subset(&parent.scopes)
            && fact.formula.bindings().iter().all(|(v, (scope, ty))| {
                parent
                    .parameters
                    .get(v)
                    .is_some_and(|p| p.scope == *scope && p.ty == *ty)
            })
            && fact.alternatives.iter().all(|f| {
                f.bindings().iter().all(|(v, (scope, ty))| {
                    parent
                        .parameters
                        .get(v)
                        .is_some_and(|p| p.scope == *scope && p.ty == *ty)
                })
            })
    }
    pub fn exportable_to(&self, parent: &Self) -> Vec<Fact> {
        if !self.shares_store_with(parent) {
            return Vec::new();
        }
        self.facts
            .iter()
            .filter_map(|fact| {
                let mut exported = fact.clone();
                exported
                    .derivations
                    .retain(|d| self.export_eligible(fact, d, parent));
                (!exported.derivations.is_empty()).then_some(exported)
            })
            .collect()
    }
    pub fn export_delta(&self, parent: &Self) -> Result<ExportDelta, ContextError> {
        if !self.shares_store_with(parent) {
            return Err(ContextError::ForeignStore);
        }
        let facts = self
            .exportable_to(parent)
            .into_iter()
            .filter_map(|mut f| {
                let identity = f.id;
                f.derivations.retain(|d| {
                    !parent.facts.iter().any(|old| {
                        old.id == identity && old.derivations.iter().any(|o| o.id == d.id)
                    })
                });
                (!f.derivations.is_empty()).then_some(f)
            })
            .collect();
        Ok(ExportDelta {
            store: self.store_id(),
            facts,
        })
    }
    pub fn import_delta(&mut self, delta: ExportDelta) -> Result<usize, ContextError> {
        if delta.store != self.store_id() {
            return Err(ContextError::ForeignStore);
        }
        for fact in &delta.facts {
            for d in &fact.derivations {
                if !self.export_eligible(fact, d, self) {
                    return Err(ContextError::InaccessibleProof(d.id));
                }
            }
        }
        let count = delta.facts.len();
        for incoming in delta.facts {
            if let Some(existing) = self.facts.iter_mut().find(|f| f.id == incoming.id) {
                for d in incoming.derivations {
                    if existing.derivations.iter().any(|old| old.dominates(&d)) {
                        continue;
                    }
                    existing.derivations.retain(|old| !d.dominates(old));
                    existing.derivations.push(d);
                }
            } else {
                self.facts.push(incoming);
            }
        }
        Ok(count)
    }
}
