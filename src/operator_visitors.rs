use std::collections::BTreeMap;

use crate::{
    Annotation, Binop, Cmp, CmpChain, Expr, Finop, Monop, RawExpr, TypeExpr, Variable,
    deep_clone::deep_clone,
    expression_utils::all_variables,
    formula::substitute_free_variable,
    type_expr::abstract_type_variable,
    type_resolver::{MaybeTyped, TypeError, TypedMetadata},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Default)]
pub struct SetOperatorLowering {
    rewrites: usize,
    error: Option<TypeError>,
}

/// Compatibility name for the original single-operator lowering pass.
pub type NulVisitor = SetOperatorLowering;

impl SetOperatorLowering {
    pub fn finish(self) -> Result<usize, TypeError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for SetOperatorLowering
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() || matches!(node.raw, RawExpr::SetComprehension { .. }) {
            return;
        }
        visit_mut::visit_expr_mut(self, context.clone(), node);
        let RawExpr::Monop(op @ (Monop::Nul | Monop::Range), operand) = &node.raw else {
            return;
        };
        let TypeExpr::Matrix(rows, columns) = (match operand.meta.get_type() {
            Ok(ty) => ty,
            Err(_) => {
                self.error = Some(TypeError::Invalid(
                    "set operators require an operand with a resolved symbolic matrix type",
                ));
                return;
            }
        }) else {
            self.error = Some(TypeError::Invalid("set operators require a matrix operand"));
            return;
        };

        let used = all_variables(std::iter::once(operand));
        let mut variable = Variable::new("x");
        while used.contains(&variable) {
            variable.annotations.push(Annotation::Prime);
        }
        let vector = Expr::with_metadata(Metadata::default(), RawExpr::Variable(variable.clone()));
        let (domain, predicate) = match op {
            Monop::Nul => {
                let product = Expr::with_metadata(
                    Metadata::default(),
                    RawExpr::Finop(Finop::Times, vec![deep_clone(operand), vector]),
                );
                let zero = Expr::with_metadata(
                    Metadata::default(),
                    RawExpr::ZeroMatrix {
                        rows: crate::ImplicitDimension::fresh(),
                        cols: crate::ImplicitDimension::fresh(),
                    },
                );
                (
                    TypeExpr::Matrix(columns.with_default_metadata(), natural(1)),
                    comparison(product, Cmp::Eq, zero),
                )
            }
            Monop::Range => {
                let predicate = if context.logical_polarity {
                    let mut witness = Variable::new("w");
                    witness.non_numeric_subscript =
                        format!("preimage of {}", operand.as_latex_verbose());
                    let witness_expression = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Variable(witness.clone()),
                    );
                    let product = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Finop(Finop::Times, vec![deep_clone(operand), witness_expression]),
                    );
                    Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Finop(
                            Finop::Exists,
                            vec![
                                Expr::with_metadata(
                                    Metadata::default(),
                                    RawExpr::Binop(
                                        Binop::ElementOf,
                                        Expr::with_metadata(
                                            Metadata::default(),
                                            RawExpr::Variable(witness),
                                        ),
                                        Expr::with_metadata(
                                            Metadata::default(),
                                            RawExpr::Type(TypeExpr::Matrix(
                                                columns.with_default_metadata(),
                                                natural(1),
                                            )),
                                        ),
                                    ),
                                ),
                                comparison(product, Cmp::Eq, vector),
                            ],
                        ),
                    )
                } else {
                    let mut counterexample = Variable::new("z");
                    counterexample.non_numeric_subscript =
                        format!("left null of {}", operand.as_latex_verbose());
                    let counterexample_expression = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Variable(counterexample.clone()),
                    );
                    let transpose_operand = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Monop(Monop::Transpose, deep_clone(operand)),
                    );
                    let left_null_product = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Finop(
                            Finop::Times,
                            vec![transpose_operand, deep_clone(&counterexample_expression)],
                        ),
                    );
                    let zero = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::ZeroMatrix {
                            rows: crate::ImplicitDimension::fresh(),
                            cols: crate::ImplicitDimension::fresh(),
                        },
                    );
                    let transpose_counterexample = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Monop(Monop::Transpose, counterexample_expression),
                    );
                    let orthogonality = Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Finop(Finop::Times, vec![transpose_counterexample, vector]),
                    );
                    Expr::with_metadata(
                        Metadata::default(),
                        RawExpr::Finop(
                            Finop::Forall,
                            vec![
                                Expr::with_metadata(
                                    Metadata::default(),
                                    RawExpr::Binop(
                                        Binop::ElementOf,
                                        Expr::with_metadata(
                                            Metadata::default(),
                                            RawExpr::Variable(counterexample),
                                        ),
                                        Expr::with_metadata(
                                            Metadata::default(),
                                            RawExpr::Type(TypeExpr::Matrix(
                                                rows.with_default_metadata(),
                                                natural(1),
                                            )),
                                        ),
                                    ),
                                ),
                                comparison(left_null_product, Cmp::Eq, zero),
                                comparison(orthogonality, Cmp::Eq, natural(0)),
                            ],
                        ),
                    )
                };
                (
                    TypeExpr::Matrix(rows.with_default_metadata(), natural(1)),
                    predicate,
                )
            }
            _ => unreachable!(),
        };
        let mut predicate = predicate;
        predicate
            .get_mut()
            .expect("new set predicates must be uniquely owned")
            .meta
            .put_type(TypeExpr::Bool);
        *node = Expr::with_metadata(
            Metadata::default(),
            RawExpr::SetComprehension {
                variable,
                domain,
                predicate,
            },
        );
        self.rewrites += 1;
    }
}

#[derive(Default)]
pub struct QuantifierLowering {
    rewrites: usize,
    error: Option<TypeError>,
    side_conditions: Vec<SideCondition<TypedMetadata>>,
    by_variable: BTreeMap<Variable, usize>,
}

/// Compatibility name for the original existential-only lowering pass.
pub type ExistsLowering = QuantifierLowering;

impl QuantifierLowering {
    pub fn finish(self) -> Result<(usize, Vec<SideCondition<TypedMetadata>>), TypeError> {
        self.error
            .map_or(Ok((self.rewrites, self.side_conditions)), Err)
    }
}

impl VisitMut<TypedMetadata> for QuantifierLowering {
    fn side_conditions(&mut self) -> Vec<SideCondition<TypedMetadata>> {
        std::mem::take(&mut self.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() || matches!(node.raw, RawExpr::SetComprehension { .. }) {
            return;
        }
        visit_mut::visit_expr_mut(self, context.clone(), node);
        let RawExpr::Finop(op @ (Finop::Exists | Finop::Forall), expressions) = &node.raw else {
            return;
        };
        let supported_polarity = match op {
            Finop::Exists => context.logical_polarity,
            Finop::Forall => !context.logical_polarity,
            _ => unreachable!(),
        };
        if !supported_polarity {
            return;
        }
        let Some((declaration, remaining)) = expressions.split_first() else {
            self.error = Some(TypeError::Invalid(
                "quantifier requires one binder declaration and a body",
            ));
            return;
        };
        if remaining.is_empty() {
            self.error = Some(TypeError::Invalid(
                "quantifier requires one binder declaration and a body",
            ));
            return;
        }
        let Some((binder, explicit_type)) = binder_declaration(declaration) else {
            self.error = Some(TypeError::Invalid(
                "quantifier requires a direct variable binder",
            ));
            return;
        };
        let binder_type = match explicit_type {
            Some(ty) => ty,
            None => match declaration.meta.get_type() {
                Ok(ty) => ty,
                Err(_) => return,
            },
        };

        let source = deep_clone(node);
        let witness_source = if remaining.len() == 1 {
            deep_clone(&remaining[0])
        } else {
            Expr::with_metadata(
                TypedMetadata::default(),
                RawExpr::Finop(Finop::And, remaining.iter().map(deep_clone).collect()),
            )
        };
        let mapped_source = wrap_in_maps(&witness_source, &context.active_ranges);
        let type_expression: Expr<TypedMetadata> = Expr::with_metadata(
            TypedMetadata::default(),
            RawExpr::Type(binder_type.with_default_metadata()),
        );
        let role = match op {
            Finop::Exists => "witness",
            Finop::Forall => "counterexample",
            _ => unreachable!(),
        };
        let introduced_variable = Variable::new(format!(
            r"\operatorname{{{role}}}\left({}; {}\right)",
            type_expression.as_latex_verbose(),
            mapped_source.as_latex_verbose()
        ));
        let introduced_type = lift_type(binder_type.clone(), &context.active_ranges);
        let introduced =
            indexed_introduced_variable(introduced_variable.clone(), &context.active_ranges);
        let mut lowered = remaining
            .iter()
            .map(|expression| {
                substitute_free_variable(&expression.with_default_metadata(), binder, &introduced)
            })
            .collect::<Vec<_>>();
        let replacement = match op {
            Finop::Exists => conjunction(lowered),
            Finop::Forall => {
                let body = lowered.pop().expect("a quantifier must have a body");
                if lowered.is_empty() {
                    body
                } else {
                    Expr::new(RawExpr::LogicChain(crate::LogicChain {
                        start: conjunction(lowered),
                        assertions: vec![(crate::Logic::Imp, body)],
                    }))
                }
            }
            _ => unreachable!(),
        };
        let condition = SideCondition {
            introduced_variable: introduced_variable.clone(),
            display_name: source.as_latex().to_string(),
            introduced_type,
            active_ranges: context.active_ranges.clone(),
            defining_assertions: Vec::new(),
            existence: Existence::Guaranteed,
        };
        if let Some(index) = self.by_variable.get(&introduced_variable).copied() {
            assert_compatible(&self.side_conditions[index], &condition);
        } else {
            self.by_variable
                .insert(introduced_variable, self.side_conditions.len());
            self.side_conditions.push(condition);
        }
        *node = replacement.with_default_metadata();
        self.rewrites += 1;
    }
}

fn conjunction(mut expressions: Vec<Expr<()>>) -> Expr<()> {
    if expressions.len() == 1 {
        expressions.pop().unwrap()
    } else {
        Expr::new(RawExpr::Finop(Finop::And, expressions))
    }
}

fn binder_declaration<Metadata>(
    expression: &Expr<Metadata>,
) -> Option<(&Variable, Option<TypeExpr<()>>)> {
    match &expression.raw {
        RawExpr::Variable(variable) => Some((variable, None)),
        RawExpr::Binop(Binop::ElementOf, left, right) => {
            let (RawExpr::Variable(variable), RawExpr::Type(ty)) = (&left.raw, &right.raw) else {
                return None;
            };
            Some((variable, Some(ty.with_default_metadata())))
        }
        _ => None,
    }
}

#[derive(Default)]
pub struct Norm2SquaredVisitor {
    rewrites: usize,
    error: Option<TypeError>,
}

impl Norm2SquaredVisitor {
    pub fn finish(self) -> Result<usize, TypeError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2SquaredVisitor
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if crate::ellipsis_elimination::is_ellipsis_sequence(node)
            || matches!(node.raw, RawExpr::SetComprehension { .. })
        {
            return;
        }
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context.clone(), node);
        let Some(operand) = norm2_squared_operand(node) else {
            return;
        };
        if let Ok(ty) = operand.meta.get_type()
            && !matches!(ty, TypeExpr::Matrix(_, _))
        {
            self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
            return;
        }
        let mut core = norm2_squared(operand);
        let raw = std::mem::replace(
            &mut core
                .get_mut()
                .expect("newly constructed 2-norm core must be uniquely owned")
                .raw,
            RawExpr::Hole,
        );
        node.get_mut()
            .expect("2-norm lowering requires uniquely owned expressions")
            .raw = raw;
        self.rewrites += 1;
    }
}

pub struct Norm2Visitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    rewrites: usize,
    error: Option<TypeError>,
}

impl<Metadata> Default for Norm2Visitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            rewrites: 0,
            error: None,
        }
    }
}

impl<Metadata> Norm2Visitor<Metadata> {
    pub fn finish(self) -> Result<(usize, Vec<SideCondition<Metadata>>), TypeError> {
        self.error
            .map_or(Ok((self.rewrites, self.roots.side_conditions)), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2Visitor<Metadata>
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        std::mem::take(&mut self.roots.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if crate::ellipsis_elimination::is_ellipsis_sequence(node)
            || matches!(node.raw, RawExpr::SetComprehension { .. })
        {
            return;
        }
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context.clone(), node);
        let RawExpr::Monop(Monop::Norm2, operand) = &node.raw else {
            return;
        };
        if let Ok(ty) = operand.meta.get_type()
            && !matches!(ty, TypeExpr::Matrix(_, _))
        {
            self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
            return;
        }
        let radicand = norm2_squared(operand);
        let introduced = match self.roots.lower(
            &context,
            node,
            radicand,
            TypeExpr::Real,
            RootExistence::Guaranteed,
        ) {
            Ok(introduced) => introduced,
            Err(error) => {
                self.error = Some(error);
                return;
            }
        };
        *node = introduced;
        self.rewrites += 1;
    }
}

pub struct SquareRootVisitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    error: Option<TypeError>,
    rewrites: usize,
}

impl<Metadata> Default for SquareRootVisitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            error: None,
            rewrites: 0,
        }
    }
}

impl<Metadata> SquareRootVisitor<Metadata> {
    pub fn finish(self) -> Result<(usize, Vec<SideCondition<Metadata>>), TypeError> {
        self.error
            .map_or(Ok((self.rewrites, self.roots.side_conditions)), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for SquareRootVisitor<Metadata>
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        std::mem::take(&mut self.roots.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if crate::ellipsis_elimination::is_ellipsis_sequence(node)
            || matches!(node.raw, RawExpr::SetComprehension { .. })
        {
            return;
        }
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context.clone(), node);
        if !is_square_root(node) {
            return;
        }
        let RawExpr::Binop(Binop::Power, base, _) = &node.raw else {
            unreachable!()
        };
        let ty = match base.meta.get_type() {
            Ok(TypeExpr::Real) => TypeExpr::Real,
            Ok(matrix @ TypeExpr::Matrix(_, _)) => matrix,
            Ok(_) => {
                self.error = Some(TypeError::Invalid(
                    "square root requires a real scalar or square real matrix",
                ));
                return;
            }
            Err(_) => return,
        };
        let existence = match ty {
            TypeExpr::Real => RootExistence::Checkable,
            TypeExpr::Matrix(_, _) => RootExistence::Assumed,
            _ => unreachable!(),
        };
        let introduced = match self
            .roots
            .lower(&context, node, deep_clone(base), ty, existence)
        {
            Ok(introduced) => introduced,
            Err(error) => {
                self.error = Some(error);
                return;
            }
        };
        *node = introduced;
        self.rewrites += 1;
    }
}

#[derive(Clone, Copy)]
enum RootExistence {
    Guaranteed,
    Checkable,
    Assumed,
}

struct PrincipalRootRegistry<Metadata> {
    side_conditions: Vec<SideCondition<Metadata>>,
    by_variable: BTreeMap<Variable, usize>,
}

impl<Metadata> Default for PrincipalRootRegistry<Metadata> {
    fn default() -> Self {
        Self {
            side_conditions: Vec::new(),
            by_variable: BTreeMap::new(),
        }
    }
}

impl<Metadata> PrincipalRootRegistry<Metadata>
where
    Metadata: Clone + Default,
{
    fn lower(
        &mut self,
        context: &VisitContext,
        source: &Expr<Metadata>,
        radicand: Expr<Metadata>,
        ty: TypeExpr<()>,
        existence: RootExistence,
    ) -> Result<Expr<Metadata>, TypeError> {
        let mapped_source = wrap_in_maps(source, &context.active_ranges);
        let introduced_variable = Variable::new(mapped_source.as_latex_verbose().to_string());
        let introduced_type = lift_type(ty.clone(), &context.active_ranges);
        // These wrappers are new syntax nodes, so the source node's metadata
        // does not describe them. Type resolution fills their default metadata.
        let introduced =
            indexed_introduced_variable(introduced_variable.clone(), &context.active_ranges);
        let square = Expr::with_metadata(
            Metadata::default(),
            RawExpr::Finop(
                Finop::Times,
                vec![deep_clone(&introduced), deep_clone(&introduced)],
            ),
        );
        let mut defining_assertions = vec![comparison(square, Cmp::Eq, deep_clone(&radicand))];
        if matches!(ty, TypeExpr::Real) {
            defining_assertions.push(comparison(deep_clone(&introduced), Cmp::Ge, natural(0)));
        }
        let existence = match existence {
            RootExistence::Guaranteed => Existence::Guaranteed,
            RootExistence::Checkable => {
                Existence::Checkable(vec![comparison(radicand, Cmp::Lt, natural(0))])
            }
            RootExistence::Assumed => Existence::Assumed,
        };
        let condition = SideCondition {
            introduced_variable: introduced_variable.clone(),
            display_name: source.as_latex().to_string(),
            introduced_type,
            active_ranges: context.active_ranges.clone(),
            defining_assertions,
            existence,
        };
        if let Some(index) = self.by_variable.get(&introduced_variable).copied() {
            assert_compatible(&self.side_conditions[index], &condition);
        } else {
            self.by_variable
                .insert(introduced_variable.clone(), self.side_conditions.len());
            self.side_conditions.push(condition);
        }
        Ok(introduced)
    }
}

fn lift_type(mut ty: TypeExpr<()>, ranges: &[crate::Range<()>]) -> TypeExpr<()> {
    for range in ranges.iter().rev() {
        ty = TypeExpr::Seq(
            Expr::new(RawExpr::Type(abstract_type_variable(
                &ty,
                &range.index_variable,
                &bound_source_position(range),
            ))),
            range_length(range),
        );
    }
    ty
}

fn bound_source_position(range: &crate::Range<()>) -> Expr<()> {
    Expr::new(RawExpr::Finop(
        Finop::Plus,
        vec![
            range.from.with_default_metadata(),
            Expr::new(RawExpr::BoundNatural(crate::DeBruijnIndex::new(0))),
            Expr::new(RawExpr::Monop(
                Monop::Neg,
                Expr::new(RawExpr::NatLiteral(1)),
            )),
        ],
    ))
}

fn indexed_introduced_variable<Metadata: Default>(
    variable: Variable,
    ranges: &[crate::Range<()>],
) -> Expr<Metadata> {
    let mut expression = Expr::with_metadata(Metadata::default(), RawExpr::Variable(variable));
    for range in ranges {
        expression = Expr::with_metadata(
            Metadata::default(),
            RawExpr::Binop(Binop::SingleSubscript, expression, range_position(range)),
        );
    }
    expression
}

fn wrap_in_maps<Metadata>(source: &Expr<Metadata>, ranges: &[crate::Range<()>]) -> Expr<Metadata>
where
    Metadata: Clone + Default,
{
    let mut expression = deep_clone(source);
    for range in ranges.iter().rev() {
        expression = Expr::with_metadata(
            Metadata::default(),
            RawExpr::Seqop(
                crate::SeqOp::Map,
                crate::Range {
                    index_variable: range.index_variable.clone(),
                    from: range.from.with_default_metadata(),
                    to: range.to.with_default_metadata(),
                },
                expression,
            ),
        );
    }
    expression
}

fn range_length<Metadata: Default>(range: &crate::Range<()>) -> Expr<Metadata> {
    plus_with_difference(&range.to, &range.from)
}

fn range_position<Metadata: Default>(range: &crate::Range<()>) -> Expr<Metadata> {
    plus_with_difference(
        &Expr::new(RawExpr::Variable(range.index_variable.clone())),
        &range.from,
    )
}

fn plus_with_difference<Metadata: Default>(
    positive: &Expr<()>,
    negative: &Expr<()>,
) -> Expr<Metadata> {
    Expr::with_metadata(
        Metadata::default(),
        RawExpr::Finop(
            Finop::Plus,
            vec![
                positive.with_default_metadata(),
                Expr::with_metadata(
                    Metadata::default(),
                    RawExpr::Monop(Monop::Neg, negative.with_default_metadata()),
                ),
                natural(1),
            ],
        ),
    )
}

fn norm2_squared_operand<Metadata>(expression: &Expr<Metadata>) -> Option<&Expr<Metadata>> {
    let RawExpr::Binop(Binop::Power, norm, exponent) = &expression.raw else {
        return None;
    };
    let RawExpr::Monop(Monop::Norm2, operand) = &norm.raw else {
        return None;
    };
    matches!(exponent.raw, RawExpr::NatLiteral(2)).then_some(operand)
}

fn norm2_squared<Metadata>(operand: &Expr<Metadata>) -> Expr<Metadata>
where
    Metadata: Clone + Default,
{
    let transpose = Expr::with_metadata(
        Metadata::default(),
        RawExpr::Monop(Monop::Transpose, deep_clone(operand)),
    );
    let product = Expr::with_metadata(
        Metadata::default(),
        RawExpr::Finop(Finop::Times, vec![transpose, deep_clone(operand)]),
    );
    Expr::with_metadata(
        Metadata::default(),
        RawExpr::Binop(
            Binop::Cast,
            Expr::with_metadata(Metadata::default(), RawExpr::Type(TypeExpr::Real)),
            product,
        ),
    )
}

fn is_square_root<Metadata>(expression: &Expr<Metadata>) -> bool {
    let RawExpr::Binop(Binop::Power, _, exponent) = &expression.raw else {
        return false;
    };
    matches!(
        &exponent.raw,
        RawExpr::Binop(Binop::Div, numerator, denominator)
            if matches!(numerator.raw, RawExpr::NatLiteral(1))
                && matches!(denominator.raw, RawExpr::NatLiteral(2))
    )
}

fn comparison<Metadata: Default>(
    left: Expr<Metadata>,
    op: Cmp,
    right: Expr<Metadata>,
) -> Expr<Metadata> {
    Expr::with_metadata(
        Metadata::default(),
        RawExpr::CmpChain(CmpChain {
            start: left,
            assertions: vec![(op, right)],
        }),
    )
}

fn natural<Metadata: Default>(value: u64) -> Expr<Metadata> {
    Expr::with_metadata(Metadata::default(), RawExpr::NatLiteral(value))
}

pub(crate) fn assert_compatible<Metadata>(
    previous: &SideCondition<Metadata>,
    current: &SideCondition<Metadata>,
) {
    assert_eq!(previous.introduced_type, current.introduced_type);
    assert_eq!(previous.active_ranges, current.active_ranges);
    assert_eq!(previous.display_name, current.display_name);
    let render = |assertions: &[Expr<Metadata>]| {
        assertions
            .iter()
            .map(|assertion| assertion.as_latex().to_string())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        render(&previous.defining_assertions),
        render(&current.defining_assertions),
        "same-named synthetic variables have incompatible definitions"
    );
    match (&previous.existence, &current.existence) {
        (Existence::Guaranteed, Existence::Guaranteed)
        | (Existence::Assumed, Existence::Assumed) => {}
        (Existence::Checkable(previous), Existence::Checkable(current)) => assert_eq!(
            render(previous),
            render(current),
            "same-named synthetic variables have incompatible existence checks"
        ),
        _ => panic!("same-named synthetic variables have incompatible existence classes"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{type_resolver::TypedMetadata, visit_mut::VisitMut};

    fn dimension(name: &str) -> Expr<()> {
        Expr::new(RawExpr::Variable(Variable::new(name)))
    }

    fn typed(ty: TypeExpr<()>, raw: RawExpr<TypedMetadata>) -> Expr<TypedMetadata> {
        Expr::with_metadata(TypedMetadata::resolved(ty), raw)
    }

    #[test]
    fn nul_lowers_to_the_right_kernel_universe() {
        let operand = typed(
            TypeExpr::Matrix(dimension("m"), dimension("n")),
            RawExpr::Variable(Variable::new("A")),
        );
        let mut expression = Expr::with_metadata(
            TypedMetadata::default(),
            RawExpr::Monop(Monop::Nul, operand),
        );
        let mut visitor = NulVisitor::default();
        visitor.visit_expr_mut(VisitContext::positive(), &mut expression);
        assert_eq!(visitor.finish(), Ok(1));
        let RawExpr::SetComprehension {
            variable,
            domain: TypeExpr::Matrix(rows, cols),
            predicate,
        } = &expression.raw
        else {
            panic!("expected a vector set comprehension")
        };
        assert_eq!(variable, &Variable::new("x"));
        assert_eq!(rows.as_latex().to_string(), "n");
        assert!(matches!(cols.raw, RawExpr::NatLiteral(1)));
        assert_eq!(predicate.as_latex().to_string(), r"A x = \mathbb{0}");
    }

    #[test]
    fn range_lowers_to_a_typed_existential_preimage() {
        let operand = typed(
            TypeExpr::Matrix(dimension("m"), dimension("n")),
            RawExpr::Variable(Variable::new("A")),
        );
        let mut expression = Expr::with_metadata(
            TypedMetadata::default(),
            RawExpr::Monop(Monop::Range, operand),
        );
        let mut visitor = SetOperatorLowering::default();
        visitor.visit_expr_mut(VisitContext::positive(), &mut expression);
        assert_eq!(visitor.finish(), Ok(1));
        let RawExpr::SetComprehension {
            domain: TypeExpr::Matrix(rows, cols),
            predicate,
            ..
        } = &expression.raw
        else {
            panic!("expected a vector set comprehension")
        };
        assert_eq!(rows.as_latex().to_string(), "m");
        assert!(matches!(cols.raw, RawExpr::NatLiteral(1)));
        assert_eq!(predicate.meta.get_type(), Ok(TypeExpr::Bool));
        assert!(matches!(predicate.raw, RawExpr::Finop(Finop::Exists, _)));
        let rendered = predicate.as_latex().to_string();
        assert!(
            rendered.contains(r"\exists w_{\text{preimage of A}}"),
            "{rendered}"
        );
        assert!(rendered.contains("A"), "{rendered}");
    }

    #[test]
    fn negative_range_lowers_to_left_null_orthogonality() {
        let operand = typed(
            TypeExpr::Matrix(dimension("m"), dimension("n")),
            RawExpr::Variable(Variable::new("A")),
        );
        let mut expression = Expr::with_metadata(
            TypedMetadata::default(),
            RawExpr::Monop(Monop::Range, operand),
        );
        let mut visitor = SetOperatorLowering::default();
        visitor.visit_expr_mut(VisitContext::negative(), &mut expression);
        assert_eq!(visitor.finish(), Ok(1));
        let RawExpr::SetComprehension { predicate, .. } = &expression.raw else {
            panic!("expected a set comprehension")
        };
        assert!(matches!(predicate.raw, RawExpr::Finop(Finop::Forall, _)));
        let rendered = predicate.as_latex().to_string();
        assert!(rendered.contains(r"A^\top"), "{rendered}");
        assert!(rendered.contains(r"\mathbb{0}"), "{rendered}");
    }

    #[test]
    fn nul_chooses_a_capture_avoiding_binder() {
        let operand = typed(
            TypeExpr::Matrix(dimension("m"), dimension("n")),
            RawExpr::Variable(Variable::new("x")),
        );
        let mut expression = Expr::with_metadata(
            TypedMetadata::default(),
            RawExpr::Monop(Monop::Nul, operand),
        );
        let mut visitor = NulVisitor::default();
        visitor.visit_expr_mut(VisitContext::positive(), &mut expression);
        assert_eq!(visitor.finish(), Ok(1));
        let RawExpr::SetComprehension { variable, .. } = &expression.raw else {
            panic!("expected a set comprehension")
        };
        assert_eq!(variable.annotations, vec![Annotation::Prime]);
    }

    #[test]
    fn nul_rejects_nonmatrix_and_untyped_operands() {
        for op in [Monop::Nul, Monop::Range] {
            for operand in [
                typed(TypeExpr::Real, RawExpr::Variable(Variable::new("a"))),
                typed(
                    TypeExpr::Set(Box::new(TypeExpr::Real)),
                    RawExpr::Variable(Variable::new("S")),
                ),
                typed(
                    TypeExpr::Seq(Expr::new(RawExpr::Type(TypeExpr::Real)), dimension("n")),
                    RawExpr::Variable(Variable::new("s")),
                ),
                Expr::with_metadata(
                    TypedMetadata::default(),
                    RawExpr::Variable(Variable::new("A")),
                ),
            ] {
                let mut expression =
                    Expr::with_metadata(TypedMetadata::default(), RawExpr::Monop(op, operand));
                let mut visitor = SetOperatorLowering::default();
                visitor.visit_expr_mut(VisitContext::positive(), &mut expression);
                assert!(visitor.finish().is_err());
            }
        }
    }
}
