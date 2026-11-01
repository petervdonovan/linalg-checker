//! Quantifier inspection uses the same lexical/type analysis as every formula.
use super::*;
use crate::{Finop, formula::free_variables};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantifierKind {
    Forall,
    Exists,
}
#[derive(Clone, Debug)]
pub struct QuantifierSpec {
    pub kind: QuantifierKind,
    pub premises: Vec<Expr<()>>,
    pub body: Expr<()>,
    pub introduced: BTreeSet<Variable>,
    pub bindings: BTreeMap<Variable, TypeExpr<()>>,
    pub questionable: Vec<Expr<()>>,
}
impl QuantifierSpec {
    pub fn is_binder_declaration(&self, e: &Expr<()>) -> bool {
        match &e.raw {
            RawExpr::Variable(v) => self.introduced.contains(v),
            RawExpr::Binop(Binop::ElementOf, left, right) => {
                matches!(&left.raw,RawExpr::Variable(v) if self.introduced.contains(v))
                    && matches!(right.raw, RawExpr::Type(_))
            }
            _ => false,
        }
    }
    pub fn from_analyzed(e: &Expr<TypedMetadata>) -> Result<Self, String> {
        let RawExpr::Finop(op @ (Finop::Forall | Finop::Exists), expressions) = &e.raw else {
            return Err("expression is not a quantifier".into());
        };
        let bindings = e
            .meta
            .quantifier_bindings()
            .ok_or("quantifier has not been analyzed")?
            .introduced
            .clone();
        let introduced = bindings.keys().cloned().collect::<BTreeSet<_>>();
        let premises = expressions[..expressions.len() - 1]
            .iter()
            .map(Expr::with_default_metadata)
            .collect::<Vec<Expr<()>>>();
        let questionable = premises
            .iter()
            .filter(|p| free_variables(std::iter::once(*p)).is_disjoint(&introduced))
            .cloned()
            .collect();
        Ok(Self {
            kind: if *op == Finop::Forall {
                QuantifierKind::Forall
            } else {
                QuantifierKind::Exists
            },
            premises,
            body: expressions.last().unwrap().with_default_metadata(),
            introduced,
            bindings,
            questionable,
        })
    }
}
pub fn analyze_quantifier(
    e: &Expr<()>,
    types: &SymbolicTypeEnvironment,
) -> Result<QuantifierSpec, String> {
    QuantifierSpec::from_analyzed(&analyze_formula(types, e).map_err(|e| e.to_string())?)
}
