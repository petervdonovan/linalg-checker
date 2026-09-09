//! Rewrite pass over expressions that eliminates anchored range ellipses.

use std::{collections::BTreeSet, error::Error, fmt};

use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

use crate::{
    Cmp, CmpChain, Expr, Finop, NaturalParameter, Range, RawExpr, SeqOp, TypeExpr, Variable,
    deep_clone::deep_clone,
    enumerable_envspec::infer_symbolic_type_environment,
    expression_utils::{
        all_variables, compare_holeifications, contains_hole, fill_holes, holeifications,
    },
    formula::{free_variables, substitute_free_variable},
    model_finding::{
        CounterexampleProgram, CounterexampleSearch, FixedEnvironmentCounterexampleChecker,
        ModelFindingError,
    },
    visit_mut::{VisitContext, VisitMut},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EllipsisEliminationError {
    UnsupportedPattern,
    NoValidCandidate,
    CounterexampleSearchUnknown,
    NoAdmissibleEnvironment,
    AnchorContainsHole,
    ModelFinding(ModelFindingError),
}

impl fmt::Display for EllipsisEliminationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedPattern => formatter.write_str(
                "ellipsis elimination currently requires one sequence of the form `a, b, ..., z`",
            ),
            Self::NoValidCandidate => formatter
                .write_str("no candidate range expression matched the visible sequence elements"),
            Self::CounterexampleSearchUnknown => {
                formatter.write_str("Z3 could not validate an ellipsis-elimination candidate")
            }
            Self::NoAdmissibleEnvironment => formatter
                .write_str("ellipsis elimination found no admissible environment for a candidate"),
            Self::AnchorContainsHole => {
                formatter.write_str("ellipsis anchors cannot contain pre-existing holes")
            }
            Self::ModelFinding(error) => error.fmt(formatter),
        }
    }
}

impl Error for EllipsisEliminationError {}

impl From<ModelFindingError> for EllipsisEliminationError {
    fn from(error: ModelFindingError) -> Self {
        Self::ModelFinding(error)
    }
}

/// Mutable traversal used while constructing collection-level rewrites.
#[derive(Default)]
pub struct EllipsisElimination;

impl EllipsisElimination {
    pub fn new() -> Self {
        Self
    }
}

impl<Metadata> VisitMut<Metadata> for EllipsisElimination {}

pub fn eliminate_ellipses<Metadata: Clone + Default>(
    expressions: &[Expr<Metadata>],
    max_dimension: u64,
) -> Result<Vec<Expr<Metadata>>, EllipsisEliminationError> {
    let untyped = expressions
        .iter()
        .map(Expr::with_default_metadata)
        .collect::<Vec<Expr<()>>>();
    let target = match supported_target(&untyped) {
        Ok(target) => target,
        Err(EllipsisEliminationError::UnsupportedPattern) => {
            return Ok(clone_forest(expressions));
        }
        Err(error) => return Err(error),
    };
    let symbolic_types =
        infer_symbolic_type_environment(&untyped).map_err(ModelFindingError::from)?;
    let variables = free_variables(untyped.iter());
    let endpoints = variables
        .iter()
        .filter(|variable| matches!(symbolic_types.types.get(*variable), Some(TypeExpr::Nat)))
        .cloned()
        .collect::<Vec<_>>();
    let index = fresh_index_variable(&all_variables(untyped.iter()));
    let bodies = candidate_bodies(&target, &index);

    let mut saw_unknown = false;
    let mut saw_admissible_environment = false;
    for body in &bodies {
        for endpoint in &endpoints {
            let candidate = map_candidate(&index, endpoint, body);
            let mut program = untyped.clone();
            program[target.expression_index] = candidate;
            program.push(minimum_endpoint(&target, endpoint));
            let Ok(search) = CounterexampleProgram::new(&program, max_dimension) else {
                continue;
            };
            let Ok(environments) = search.environments() else {
                continue;
            };
            let mut saw_environment = false;
            let mut candidate_valid = true;
            for environment in environments {
                let environment = match environment {
                    Ok(environment) => environment,
                    Err(_) => {
                        candidate_valid = false;
                        break;
                    }
                };
                saw_environment = true;
                saw_admissible_environment = true;
                let endpoint_value = environment
                    .natural_assignment
                    .get(&NaturalParameter::Variable(endpoint.clone()));
                let Some(endpoint_value) = endpoint_value.copied() else {
                    candidate_valid = false;
                    break;
                };
                let Ok(mut checker) = search.checker(&environment) else {
                    candidate_valid = false;
                    break;
                };
                match validate_positionings(&target, endpoint_value, &index, body, &mut checker) {
                    Ok(CounterexampleSearch::NotFound) => {}
                    Ok(CounterexampleSearch::Unknown) => {
                        saw_unknown = true;
                        candidate_valid = false;
                        break;
                    }
                    Ok(CounterexampleSearch::Found) | Err(_) => {
                        candidate_valid = false;
                        break;
                    }
                }
            }
            if candidate_valid && saw_environment {
                return Ok(expressions
                    .iter()
                    .enumerate()
                    .map(|(expression_index, expression)| {
                        if expression_index == target.expression_index {
                            program[expression_index].with_default_metadata()
                        } else {
                            let mut rewritten = deep_clone(expression);
                            EllipsisElimination::new()
                                .visit_expr_mut(VisitContext::positive(), &mut rewritten);
                            rewritten
                        }
                    })
                    .collect());
            }
        }
    }
    if saw_unknown {
        Err(EllipsisEliminationError::CounterexampleSearchUnknown)
    } else if !saw_admissible_environment {
        Err(EllipsisEliminationError::NoAdmissibleEnvironment)
    } else {
        Err(EllipsisEliminationError::NoValidCandidate)
    }
}

fn clone_forest<Metadata: Clone>(expressions: &[Expr<Metadata>]) -> Vec<Expr<Metadata>> {
    expressions
        .iter()
        .map(|expression| {
            let mut rewritten = deep_clone(expression);
            EllipsisElimination::new().visit_expr_mut(VisitContext::positive(), &mut rewritten);
            rewritten
        })
        .collect()
}

struct Target<'a> {
    expression_index: usize,
    elements: &'a [Expr<()>],
}

impl Target<'_> {
    fn anchors(&self) -> Vec<(usize, &Expr<()>)> {
        self.elements
            .iter()
            .enumerate()
            .filter(|(_, expression)| !matches!(expression.raw, RawExpr::Ellipsis))
            .collect()
    }
}

fn supported_target(expressions: &[Expr<()>]) -> Result<Target<'_>, EllipsisEliminationError> {
    let mut targets = expressions
        .iter()
        .enumerate()
        .filter_map(|(index, expression)| {
            let RawExpr::Finop(Finop::SeqLiteral, elements) = &expression.raw else {
                return None;
            };
            elements
                .iter()
                .any(|element| matches!(element.raw, RawExpr::Ellipsis))
                .then_some(Target {
                    expression_index: index,
                    elements,
                })
        });
    let target = targets
        .next()
        .ok_or(EllipsisEliminationError::UnsupportedPattern)?;
    struct EllipsisCounter(usize);
    impl crate::visit::Visit<()> for EllipsisCounter {
        fn visit_raw_expr_ellipsis(&mut self) {
            self.0 += 1;
        }
    }
    let mut counter = EllipsisCounter(0);
    for expression in expressions {
        crate::visit::Visit::visit_expr(&mut counter, expression);
    }
    let target_ellipsis_count = target
        .elements
        .iter()
        .filter(|element| matches!(element.raw, RawExpr::Ellipsis))
        .count();
    if target
        .anchors()
        .into_iter()
        .any(|(_, anchor)| contains_hole(anchor))
    {
        return Err(EllipsisEliminationError::AnchorContainsHole);
    }
    if targets.next().is_some() || counter.0 != target_ellipsis_count || target.anchors().is_empty()
    {
        return Err(EllipsisEliminationError::UnsupportedPattern);
    }
    Ok(target)
}

fn candidate_bodies(target: &Target<'_>, index: &Variable) -> Vec<Expr<()>> {
    let mut patterns = target
        .anchors()
        .into_iter()
        .flat_map(|(_, anchor)| holeifications(anchor))
        .collect::<Vec<_>>();
    patterns.sort_by(compare_holeifications);
    patterns.dedup();

    let index = Expr::new(RawExpr::Variable(index.clone()));
    let mut seen = BTreeSet::new();
    patterns
        .into_iter()
        .map(|pattern| fill_holes(&pattern, &index))
        .filter(|body| seen.insert(body.clone()))
        .collect()
}

fn fresh_index_variable(variables: &std::collections::BTreeSet<Variable>) -> Variable {
    ["i", "j", "k", "l", "m"]
        .iter()
        .map(|name| Variable::new(*name))
        .find(|variable| !variables.contains(variable))
        .expect("ellipsis elimination ran out of supported index-variable names")
}

fn map_candidate(index: &Variable, endpoint: &Variable, body: &Expr<()>) -> Expr<()> {
    Expr::new(RawExpr::Seqop(
        SeqOp::Map,
        Range {
            index_variable: index.clone(),
            from: Expr::new(RawExpr::NatLiteral(1)),
            to: Expr::new(RawExpr::Variable(endpoint.clone())),
        },
        body.clone(),
    ))
}

fn minimum_endpoint(target: &Target<'_>, endpoint: &Variable) -> Expr<()> {
    let anchor_count =
        u64::try_from(target.anchors().len()).expect("ellipsis anchor count does not fit in u64");
    Expr::new(RawExpr::CmpChain(CmpChain {
        start: Expr::new(RawExpr::NatLiteral(anchor_count)),
        assertions: vec![(Cmp::Le, Expr::new(RawExpr::Variable(endpoint.clone())))],
    }))
}

fn validate_positionings(
    target: &Target<'_>,
    endpoint: u64,
    index: &Variable,
    body: &Expr<()>,
    checker: &mut FixedEnvironmentCounterexampleChecker<'_>,
) -> Result<CounterexampleSearch, ModelFindingError> {
    let anchors = target.anchors();
    let positions = (0..anchors.len())
        .map(|anchor_index| Int::new_const(format!("__ellipsis_anchor_position_{anchor_index}")))
        .collect::<Vec<_>>();
    let solver = Solver::new();
    let one = Int::from_u64(1);
    let endpoint_value = Int::from_u64(endpoint);
    for position in &positions {
        solver.assert(position.ge(&one));
        solver.assert(position.le(&endpoint_value));
    }
    if anchors[0].0 == 0 {
        solver.assert(positions[0].eq(&one));
    }
    if anchors.last().unwrap().0 + 1 == target.elements.len() {
        solver.assert(positions.last().unwrap().eq(&endpoint_value));
    }
    for (anchor_pair, position_pair) in anchors.windows(2).zip(positions.windows(2)) {
        if anchor_pair[1].0 == anchor_pair[0].0 + 1 {
            solver.assert(position_pair[1].eq(Int::add(&[position_pair[0].clone(), one.clone()])));
        } else {
            solver.assert(position_pair[0].lt(&position_pair[1]));
        }
    }

    let mut saw_unknown = false;
    loop {
        match solver.check() {
            SatResult::Unsat => {
                return Ok(if saw_unknown {
                    CounterexampleSearch::Unknown
                } else {
                    CounterexampleSearch::Found
                });
            }
            SatResult::Unknown => return Ok(CounterexampleSearch::Unknown),
            SatResult::Sat => {}
        }
        let model = solver.get_model().ok_or(ModelFindingError::MissingModel)?;
        let values = positions
            .iter()
            .map(|position| {
                model
                    .eval(position, false)
                    .and_then(|value| value.as_u64())
                    .ok_or(ModelFindingError::ModelValueOutOfRange(
                        "ellipsis anchor position is not a natural numeral",
                    ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let claims = anchors
            .iter()
            .zip(&values)
            .map(|((_, anchor), position)| {
                equality(
                    substitute_free_variable(
                        body,
                        index,
                        &Expr::new(RawExpr::NatLiteral(*position)),
                    ),
                    (*anchor).clone(),
                )
            })
            .collect::<Vec<_>>();
        match checker.check(&claims)? {
            CounterexampleSearch::NotFound => return Ok(CounterexampleSearch::NotFound),
            CounterexampleSearch::Unknown => saw_unknown = true,
            CounterexampleSearch::Found => {}
        }
        let blocker = positions
            .iter()
            .zip(values)
            .map(|(position, value)| position.eq(Int::from_u64(value)).not())
            .collect::<Vec<_>>();
        solver.assert(Bool::or(&blocker));
    }
}

fn equality(left: Expr<()>, right: Expr<()>) -> Expr<()> {
    Expr::new(RawExpr::CmpChain(CmpChain {
        start: left,
        assertions: vec![(Cmp::Eq, right)],
    }))
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::{EllipsisEliminationError, eliminate_ellipses};
    use crate::{
        Environment, Expr, Finop, RawExpr,
        elaboration::{ElaborationError, elaborate},
        from_tex,
        preprocessing::PreparedExpression,
        type_resolver::TypedMetadata,
        visit::{self, Visit},
        visit_mut::{VisitContext, VisitMut},
    };

    #[test]
    fn eliminates_a_natural_range_into_a_unique_map() {
        let original: Expr<()> = from_tex::expr(&parse(r"1, 2, \ldots, n").unwrap()).unwrap();
        let mut rewritten = eliminate_ellipses(std::slice::from_ref(&original), 3)
            .unwrap()
            .pop()
            .unwrap();
        let rewritten_node = rewritten
            .get_mut()
            .expect("rewritten root should be uniquely owned");
        let RawExpr::Seqop(_, range, body) = &mut rewritten_node.raw else {
            panic!("expected a map")
        };
        assert!(range.from.get_mut().is_some());
        assert!(range.to.get_mut().is_some());
        assert!(body.get_mut().is_some());
        assert_eq!(
            rewritten.as_latex().to_string(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
        assert_eq!(original.as_latex().to_string(), r"1, 2, \ldots, n");
    }

    #[test]
    fn rejects_a_candidate_with_a_visible_counterexample() {
        let original: Expr<()> = from_tex::expr(&parse(r"1, 3, \ldots, n").unwrap()).unwrap();
        assert!(matches!(
            eliminate_ellipses(std::slice::from_ref(&original), 3),
            Err(EllipsisEliminationError::NoValidCandidate)
        ));
    }

    #[test]
    fn selects_the_endpoint_valid_across_the_environment_family() {
        let expressions = [r"m \in \mathbb{N}", r"n \in \mathbb{N}", r"1, 2, \ldots, n"]
            .map(|tex| from_tex::expr(&parse(tex).unwrap()).unwrap());
        let rewritten = eliminate_ellipses(&expressions, 4).unwrap();
        assert_eq!(
            rewritten[2].as_latex().to_string(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
    }

    fn rewrite_last(
        expressions: &[&str],
        max_dimension: u64,
    ) -> Result<String, EllipsisEliminationError> {
        let expressions = expressions
            .iter()
            .map(|tex| from_tex::expr(&parse(tex).unwrap()).unwrap())
            .collect::<Vec<Expr<()>>>();
        eliminate_ellipses(&expressions, max_dimension)
            .map(|rewritten| rewritten.last().unwrap().as_latex().to_string())
    }

    #[test]
    fn supports_general_anchor_layouts() {
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"\ldots, n"], 3).unwrap(),
            r"\operatorname{map}_{i=1}^{n}n"
        );
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"1, \ldots"], 3).unwrap(),
            r"\operatorname{map}_{i=1}^{n}1"
        );
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"2 \le n", r"1, 2, \ldots"], 3,).unwrap(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"2 \le n", r"\ldots, n - 1, n",], 3,).unwrap(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"1, \ldots, \ldots, n"], 3,).unwrap(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
        assert_eq!(
            rewrite_last(
                &[
                    r"n \in \mathbb{N}",
                    r"6 \le n",
                    r"1, 2, \ldots, 4, 5, \ldots, n",
                ],
                6,
            )
            .unwrap(),
            r"\operatorname{map}_{i=1}^{n}i"
        );
    }

    #[test]
    fn accepts_one_proven_positioning_and_rejects_when_none_work() {
        let declarations = [
            r"n \in \mathbb{N}",
            r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            r"4 \le n",
        ];
        let valid = declarations
            .into_iter()
            .chain([r"c_1, \ldots, c_3, \ldots, c_n"])
            .collect::<Vec<_>>();
        assert_eq!(
            rewrite_last(&valid, 4).unwrap(),
            r"\operatorname{map}_{i=1}^{n}c_{i}"
        );

        let invalid = [
            r"n \in \mathbb{N}",
            r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
            r"d \in \operatorname{Seq}_{n}(\mathbb{R})",
            r"4 \le n",
            r"c_1, \ldots, d_3, \ldots, c_n",
        ];
        assert!(matches!(
            rewrite_last(&invalid, 4),
            Err(EllipsisEliminationError::NoValidCandidate)
        ));
    }

    #[test]
    fn derives_compound_bodies_from_anchor_subterms() {
        assert_eq!(
            rewrite_last(
                &[
                    r"n \in \mathbb{N}",
                    r"c \in \operatorname{Seq}_{n}(\mathbb{R})",
                    r"c_1^2, \ldots, c_n^2",
                ],
                3,
            )
            .unwrap(),
            r"\operatorname{map}_{i=1}^{n}c_{i}^{2}"
        );
        assert_eq!(
            rewrite_last(
                &[r"n \in \mathbb{N}", r"3 \le n", r"2, 3, \ldots, n + 1"],
                3,
            )
            .unwrap(),
            r"\operatorname{map}_{i=1}^{n}\left(i + 1\right)"
        );
    }

    #[test]
    fn exact_constant_body_precedes_a_valid_generalization() {
        assert_eq!(
            rewrite_last(&[r"n \in \mathbb{N}", r"1, \ldots, 1"], 3).unwrap(),
            r"\operatorname{map}_{i=1}^{n}1"
        );
    }

    #[test]
    fn generated_index_does_not_capture_an_anchor_binder() {
        assert_eq!(
            rewrite_last(
                &[
                    r"n \in \mathbb{N}",
                    r"3 \le n",
                    r"\sum_{i=1}^{1} i, \sum_{i=1}^{2} i, \ldots, \sum_{i=1}^{n} i",
                ],
                3,
            )
            .unwrap(),
            r"\operatorname{map}_{j=1}^{n}\sum_{i=1}^{j}i"
        );
    }

    #[test]
    fn rejects_preexisting_holes_in_anchors() {
        assert!(matches!(
            rewrite_last(&[r"n \in \mathbb{N}", r"\square, \ldots, n"], 3),
            Err(EllipsisEliminationError::AnchorContainsHole)
        ));
    }

    #[test]
    fn preserves_an_ellipsis_sequence_without_anchors() {
        assert_eq!(
            rewrite_last(&[r"\ldots, \ldots"], 3).unwrap(),
            r"\ldots, \ldots"
        );
    }

    #[test]
    fn rejects_vacuous_candidate_validation() {
        assert!(matches!(
            rewrite_last(&[r"n \in \mathbb{N}", r"3 < n", r"1, 2, \ldots, n"], 3,),
            Err(EllipsisEliminationError::NoAdmissibleEnvironment)
        ));
    }

    #[test]
    fn immutable_and_mutable_visitors_expose_ellipsis_hooks() {
        struct ImmutableCounter(usize);
        impl Visit<()> for ImmutableCounter {
            fn visit_raw_expr_ellipsis(&mut self) {
                self.0 += 1;
                visit::visit_raw_expr_ellipsis(self);
            }
        }
        struct MutableCounter(usize);
        impl VisitMut<()> for MutableCounter {
            fn visit_raw_expr_ellipsis_mut(&mut self, _context: VisitContext) {
                self.0 += 1;
            }
        }

        let expression = Expr::new(RawExpr::Finop(
            Finop::SeqLiteral,
            vec![Expr::new(RawExpr::Ellipsis), Expr::new(RawExpr::Ellipsis)],
        ));
        let mut immutable = ImmutableCounter(0);
        immutable.visit_expr(&expression);
        assert_eq!(immutable.0, 2);

        let mut expression = expression.with_default_metadata();
        let mut mutable = MutableCounter(0);
        mutable.visit_expr_mut(VisitContext::positive(), &mut expression);
        assert_eq!(mutable.0, 2);
    }

    #[test]
    fn concrete_elaboration_rejects_an_uneliminated_ellipsis() {
        let prepared = PreparedExpression {
            expression: Expr::with_metadata(TypedMetadata::default(), RawExpr::Ellipsis),
            side_conditions: Vec::new(),
            context: VisitContext::positive(),
        };
        assert!(matches!(
            elaborate(&Environment::default(), &prepared),
            Err(ElaborationError::Unsupported(
                "ellipses must be eliminated before Z3 lowering"
            ))
        ));
    }
}
