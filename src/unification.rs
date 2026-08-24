use std::collections::{BTreeMap, BTreeSet};

use crate::{
    Expr, Finop, ImplicitDimension, RawExpr, TypeExpr, Variable,
    formula::{free_variables, quantifier_binders},
};

pub(crate) struct Unifier<'a> {
    pub(crate) metavariables: &'a BTreeSet<Variable>,
    pub(crate) assignments: BTreeMap<Variable, Expr<()>>,
    pub(crate) pattern_accessible: BTreeSet<Variable>,
    pub(crate) candidate_accessible: BTreeSet<Variable>,
    pub(crate) pattern_bound: BTreeSet<Variable>,
    pub(crate) candidate_bound: BTreeSet<Variable>,
    pub(crate) bound_forward: BTreeMap<Variable, Variable>,
    pub(crate) bound_reverse: BTreeMap<Variable, Variable>,
    pub(crate) nonce_pairs: BTreeSet<(ImplicitDimension, ImplicitDimension)>,
}

impl Unifier<'_> {
    pub(crate) fn expression(&mut self, pattern: &Expr<()>, candidate: &Expr<()>) -> bool {
        if let (RawExpr::Variable(pattern), RawExpr::Variable(candidate)) =
            (&pattern.raw, &candidate.raw)
            && (self.pattern_bound.contains(pattern) || self.candidate_bound.contains(candidate))
        {
            return self.bound_variable(pattern, candidate);
        }
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
            (RawExpr::ImplicitDimension(a), RawExpr::ImplicitDimension(b)) => self.nonce(*a, *b),
            (
                RawExpr::IdentityMatrix { dimension: a },
                RawExpr::IdentityMatrix { dimension: b },
            ) => self.nonce(*a, *b),
            (
                RawExpr::StandardBasis {
                    index: ai,
                    dimension: ad,
                },
                RawExpr::StandardBasis {
                    index: bi,
                    dimension: bd,
                },
            ) => self.nonce(*ad, *bd) && self.expression(ai, bi),
            (
                RawExpr::ZeroMatrix { rows: ar, cols: ac },
                RawExpr::ZeroMatrix { rows: br, cols: bc },
            ) => self.nonce(*ar, *br) && self.nonce(*ac, *bc),
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
                    && self.expression(&ar.from, &br.from)
                    && self.expression(&ar.to, &br.to)
                    && self.bound_sequence_body(&ar.index_variable, &br.index_variable, ab, bb)
            }
            _ => false,
        }
    }

    fn nonce(&mut self, pattern: ImplicitDimension, candidate: ImplicitDimension) -> bool {
        self.nonce_pairs.insert((pattern, candidate));
        true
    }

    fn bound_variable(&mut self, pattern: &Variable, candidate: &Variable) -> bool {
        if !self.pattern_bound.contains(pattern) || !self.candidate_bound.contains(candidate) {
            return false;
        }
        match (
            self.bound_forward.get(pattern),
            self.bound_reverse.get(candidate),
        ) {
            (Some(mapped), Some(reverse)) => mapped == candidate && reverse == pattern,
            (None, None) => {
                self.bound_forward
                    .insert(pattern.clone(), candidate.clone());
                self.bound_reverse
                    .insert(candidate.clone(), pattern.clone());
                true
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
        let old_bound_forward = self.bound_forward.clone();
        let old_bound_reverse = self.bound_reverse.clone();
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
        self.bound_forward = old_bound_forward;
        self.bound_reverse = old_bound_reverse;
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
        let old_bound_forward = self.bound_forward.clone();
        let old_bound_reverse = self.bound_reverse.clone();
        let matched = self.expression(pattern, candidate);
        if !pattern_was_bound {
            self.pattern_bound.remove(pattern_index);
        }
        if !candidate_was_bound {
            self.candidate_bound.remove(candidate_index);
        }
        self.bound_forward = old_bound_forward;
        self.bound_reverse = old_bound_reverse;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Range, SeqOp};

    fn expression(tex: &str) -> Expr<()> {
        crate::from_tex::expr(&ratex_parser::parse(tex).unwrap()).unwrap()
    }

    fn unifier<'a>(metavariables: &'a BTreeSet<Variable>) -> Unifier<'a> {
        Unifier {
            metavariables,
            assignments: BTreeMap::new(),
            pattern_accessible: BTreeSet::new(),
            candidate_accessible: BTreeSet::new(),
            pattern_bound: BTreeSet::new(),
            candidate_bound: BTreeSet::new(),
            bound_forward: BTreeMap::new(),
            bound_reverse: BTreeMap::new(),
            nonce_pairs: BTreeSet::new(),
        }
    }

    #[test]
    fn context_dependent_constants_match_modulo_nonce_names() {
        let empty = BTreeSet::new();
        for (pattern, candidate, expected_pairs) in [
            ("I", "I", 1),
            (r"\mathbb{0}", r"\mathbb{0}", 2),
            ("e_{1}", "e_{1}", 1),
        ] {
            let mut unifier = unifier(&empty);
            assert!(unifier.expression(&expression(pattern), &expression(candidate)));
            assert_eq!(unifier.nonce_pairs.len(), expected_pairs);
        }

        let pattern_dimension = crate::ImplicitDimension::fresh();
        let candidate_dimension = crate::ImplicitDimension::fresh();
        let mut unifier = unifier(&empty);
        assert!(unifier.expression(
            &Expr::new(RawExpr::ImplicitDimension(pattern_dimension)),
            &Expr::new(RawExpr::ImplicitDimension(candidate_dimension)),
        ));
        assert_eq!(
            unifier.nonce_pairs,
            BTreeSet::from([(pattern_dimension, candidate_dimension)])
        );
    }

    #[test]
    fn lexical_binders_match_by_correspondence_but_free_variables_do_not() {
        let empty = BTreeSet::new();
        let mut quantified = unifier(&empty);
        assert!(quantified.expression(
            &expression(r"\forall x \in \mathbb{R}, x = x"),
            &expression(r"\forall y \in \mathbb{R}, y = y"),
        ));

        let mut free = unifier(&empty);
        assert!(!free.expression(&expression("x = x"), &expression("y = y")));

        let sequence = |index: &str| {
            let index = Variable::new(index);
            Expr::new(RawExpr::Seqop(
                SeqOp::Sum,
                Range {
                    index_variable: index.clone(),
                    from: Expr::new(RawExpr::NatLiteral(1)),
                    to: Expr::new(RawExpr::NatLiteral(2)),
                },
                Expr::new(RawExpr::Variable(index)),
            ))
        };
        let mut sequence_unifier = unifier(&empty);
        assert!(sequence_unifier.expression(&sequence("i"), &sequence("j")));
    }
}
