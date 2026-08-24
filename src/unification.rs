use std::collections::{BTreeMap, BTreeSet};

use crate::{
    Expr, Finop, RawExpr, TypeExpr, Variable,
    formula::{free_variables, quantifier_binders},
};

pub(crate) struct Unifier<'a> {
    pub(crate) metavariables: &'a BTreeSet<Variable>,
    pub(crate) assignments: BTreeMap<Variable, Expr<()>>,
    pub(crate) pattern_accessible: BTreeSet<Variable>,
    pub(crate) candidate_accessible: BTreeSet<Variable>,
    pub(crate) pattern_bound: BTreeSet<Variable>,
    pub(crate) candidate_bound: BTreeSet<Variable>,
}

impl Unifier<'_> {
    pub(crate) fn expression(&mut self, pattern: &Expr<()>, candidate: &Expr<()>) -> bool {
        if let RawExpr::Variable(variable) = &pattern.raw
            && self.metavariables.contains(variable)
            && !self.pattern_bound.contains(variable)
        {
            if !free_variables(std::iter::once(candidate)).is_disjoint(&self.candidate_bound) {
                return false;
            }
            return match self.assignments.get(variable) {
                Some(assigned) => assigned == candidate,
                None => {
                    self.assignments.insert(variable.clone(), candidate.clone());
                    true
                }
            };
        }
        match (&pattern.raw, &candidate.raw) {
            (RawExpr::Hole, RawExpr::Hole) => true,
            (RawExpr::ImplicitDimension(a), RawExpr::ImplicitDimension(b)) => a == b,
            (
                RawExpr::IdentityMatrix { dimension: a },
                RawExpr::IdentityMatrix { dimension: b },
            ) => a == b,
            (
                RawExpr::StandardBasis {
                    index: ai,
                    dimension: ad,
                },
                RawExpr::StandardBasis {
                    index: bi,
                    dimension: bd,
                },
            ) => ad == bd && self.expression(ai, bi),
            (
                RawExpr::ZeroMatrix { rows: ar, cols: ac },
                RawExpr::ZeroMatrix { rows: br, cols: bc },
            ) => ar == br && ac == bc,
            (RawExpr::Type(a), RawExpr::Type(b)) => self.type_expr(a, b),
            (RawExpr::Variable(a), RawExpr::Variable(b)) => a == b,
            (RawExpr::NatLiteral(a), RawExpr::NatLiteral(b)) => a == b,
            (RawExpr::Matrix(a), RawExpr::Matrix(b)) => {
                a.rows == b.rows && a.cols == b.cols && self.expressions(&a.elements, &b.elements)
            }
            (RawExpr::Monop(ao, a), RawExpr::Monop(bo, b)) => ao == bo && self.expression(a, b),
            (RawExpr::Binop(ao, al, ar), RawExpr::Binop(bo, bl, br)) => {
                ao == bo && self.expression(al, bl) && self.expression(ar, br)
            }
            (RawExpr::Triop(ao, aa, ab, ac), RawExpr::Triop(bo, ba, bb, bc)) => {
                ao == bo
                    && self.expression(aa, ba)
                    && self.expression(ab, bb)
                    && self.expression(ac, bc)
            }
            (RawExpr::Finop(ao, a), RawExpr::Finop(bo, b)) if ao == bo => {
                if matches!(ao, Finop::Forall | Finop::Exists) {
                    self.quantified_expressions(a, b)
                } else {
                    self.expressions(a, b)
                }
            }
            (RawExpr::CmpChain(a), RawExpr::CmpChain(b)) => {
                a.assertions.len() == b.assertions.len()
                    && self.expression(&a.start, &b.start)
                    && a.assertions
                        .iter()
                        .zip(&b.assertions)
                        .all(|((ao, ae), (bo, be))| ao == bo && self.expression(ae, be))
            }
            (RawExpr::LogicChain(a), RawExpr::LogicChain(b)) => {
                a.assertions.len() == b.assertions.len()
                    && self.expression(&a.start, &b.start)
                    && a.assertions
                        .iter()
                        .zip(&b.assertions)
                        .all(|((ao, ae), (bo, be))| ao == bo && self.expression(ae, be))
            }
            (RawExpr::Seqop(ao, ar, ab), RawExpr::Seqop(bo, br, bb)) => {
                ao == bo
                    && ar.index_variable == br.index_variable
                    && self.expression(&ar.from, &br.from)
                    && self.expression(&ar.to, &br.to)
                    && self.bound_sequence_body(&ar.index_variable, &br.index_variable, ab, bb)
            }
            _ => false,
        }
    }

    fn expressions(&mut self, pattern: &[Expr<()>], candidate: &[Expr<()>]) -> bool {
        pattern.len() == candidate.len()
            && pattern
                .iter()
                .zip(candidate)
                .all(|(pattern, candidate)| self.expression(pattern, candidate))
    }

    fn quantified_expressions(&mut self, pattern: &[Expr<()>], candidate: &[Expr<()>]) -> bool {
        if pattern.len() != candidate.len() {
            return false;
        }
        let pattern_binders = quantifier_binders(pattern, &self.pattern_accessible);
        let candidate_binders = quantifier_binders(candidate, &self.candidate_accessible);
        let old_pattern_bound = self.pattern_bound.clone();
        let old_candidate_bound = self.candidate_bound.clone();
        let old_pattern_accessible = self.pattern_accessible.clone();
        let old_candidate_accessible = self.candidate_accessible.clone();
        self.pattern_bound.extend(pattern_binders.iter().cloned());
        self.candidate_bound
            .extend(candidate_binders.iter().cloned());
        self.pattern_accessible.extend(pattern_binders);
        self.candidate_accessible.extend(candidate_binders);
        let matched = self.expressions(pattern, candidate);
        self.pattern_bound = old_pattern_bound;
        self.candidate_bound = old_candidate_bound;
        self.pattern_accessible = old_pattern_accessible;
        self.candidate_accessible = old_candidate_accessible;
        matched
    }

    fn bound_sequence_body(
        &mut self,
        pattern_index: &Variable,
        candidate_index: &Variable,
        pattern: &Expr<()>,
        candidate: &Expr<()>,
    ) -> bool {
        let pattern_was_bound = !self.pattern_bound.insert(pattern_index.clone());
        let candidate_was_bound = !self.candidate_bound.insert(candidate_index.clone());
        let matched = self.expression(pattern, candidate);
        if !pattern_was_bound {
            self.pattern_bound.remove(pattern_index);
        }
        if !candidate_was_bound {
            self.candidate_bound.remove(candidate_index);
        }
        matched
    }

    fn type_expr(&mut self, pattern: &TypeExpr<()>, candidate: &TypeExpr<()>) -> bool {
        match (pattern, candidate) {
            (TypeExpr::Bool, TypeExpr::Bool)
            | (TypeExpr::Nat, TypeExpr::Nat)
            | (TypeExpr::Int, TypeExpr::Int)
            | (TypeExpr::Real, TypeExpr::Real) => true,
            (TypeExpr::Matrix(ar, ac), TypeExpr::Matrix(br, bc))
            | (TypeExpr::Seq(ar, ac), TypeExpr::Seq(br, bc)) => {
                self.expression(ar, br) && self.expression(ac, bc)
            }
            _ => false,
        }
    }
}
