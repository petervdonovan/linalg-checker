use super::*;
use crate::type_resolver::{TypeError, TypedMetadata};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckedData {
    id: InterpretationId,
    store: StoreId,
    written: Expr<()>,
    analyzed: Expr<TypedMetadata>,
    bindings: BTreeMap<Variable, (ScopeId, TypeExpr<()>)>,
}
/// An immutable meaning whose lexical binding/type analysis succeeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedFormula(Rc<CheckedData>);
impl CheckedFormula {
    pub fn id(&self) -> InterpretationId {
        self.0.id
    }
    pub fn written(&self) -> &Expr<()> {
        &self.0.written
    }
    pub fn analyzed(&self) -> &Expr<TypedMetadata> {
        &self.0.analyzed
    }
    pub fn meaning(&self) -> Expr<()> {
        self.0.analyzed.with_default_metadata()
    }
    pub fn free_variables(&self) -> &BTreeSet<Variable> {
        self.0
            .analyzed
            .meta
            .free_variables
            .as_ref()
            .expect("checked formula has binding analysis")
    }
    pub(crate) fn store(&self) -> StoreId {
        self.0.store
    }
    pub(crate) fn bindings(&self) -> &BTreeMap<Variable, (ScopeId, TypeExpr<()>)> {
        &self.0.bindings
    }
    pub(crate) fn same_meaning(&self, other: &Self) -> bool {
        self.0.store == other.0.store
            && self.0.bindings == other.0.bindings
            && self.0.analyzed == other.0.analyzed
    }
    pub(crate) fn from_interpreted(
        context: &ProofContext,
        written: &Expr<()>,
        meaning: Expr<()>,
    ) -> Result<Self, TypeError> {
        let meaning = crate::type_resolver::analyze_formula(&context.types, &meaning)?;
        if crate::ellipsis_elimination::contains_ellipses(&meaning) {
            return Err(TypeError::Invalid(
                "formula interpretation still contains ellipses",
            ));
        }
        let free = meaning
            .meta
            .free_variables
            .as_ref()
            .ok_or(TypeError::Invalid(
                "formula has no lexical binding analysis",
            ))?;
        let bindings = free
            .iter()
            .map(|v| {
                context
                    .parameters
                    .get(v)
                    .map(|p| (v.clone(), (p.scope, p.ty.clone())))
                    .ok_or_else(|| TypeError::UndefinedVariable(v.clone()))
            })
            .collect::<Result<_, _>>()?;
        Ok(Self(Rc::new(CheckedData {
            id: InterpretationId(super::context::fresh()),
            store: context.store_id(),
            written: written.clone(),
            analyzed: meaning,
            bindings,
        })))
    }
}

/// Interpretation is an explicit service, independent of rule matching and
/// concrete SMT lowering. Provisional witness scopes use the same service.
pub trait FormulaInterpreter {
    fn check(
        &self,
        context: &ProofContext,
        written: &Expr<()>,
    ) -> Result<CheckedFormula, TypeError>;
}
pub struct SurfaceInterpreter;
impl FormulaInterpreter for SurfaceInterpreter {
    fn check(
        &self,
        context: &ProofContext,
        written: &Expr<()>,
    ) -> Result<CheckedFormula, TypeError> {
        context.check(written)
    }
}
