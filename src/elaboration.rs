//! Environment-specific elaboration of symbolically typed expressions.
//!
//! This phase runs after environment enumeration. It specializes symbolic
//! dimensions and removes operations whose meaning depends on concrete matrix
//! or sequence sizes, leaving only scalar operations and flat matrix values.

use std::{error::Error, fmt};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Logic, LogicChain, Matrix, Monop,
    NaturalEvaluationError, NaturalParameter, Range, RawExpr, SeqOp, TypeExpr, Variable,
    deep_clone::deep_clone,
    preprocessing::PreparedExpression,
    type_expr::{contains_unbound_natural, open_sequence_element, substitute_type_variable},
    type_resolver::{MaybeTyped, TypeError, TypedMetadata},
    visit::{self, Visit},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Clone, Debug)]
pub struct ElaboratedExpression {
    pub expression: Expr<TypedMetadata>,
    pub side_conditions: Vec<SideCondition<TypedMetadata>>,
    pub context: VisitContext,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElaborationError {
    Type(TypeError),
    Natural(NaturalEvaluationError),
    Unsupported(&'static str),
    InvalidOperands(&'static str),
    Shape(&'static str),
    Empty(&'static str),
    DimensionOverflow,
    InvalidMatrixLiteral,
}

impl fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(error) => error.fmt(f),
            Self::Natural(error) => error.fmt(f),
            Self::Unsupported(message)
            | Self::InvalidOperands(message)
            | Self::Shape(message)
            | Self::Empty(message) => f.write_str(message),
            Self::DimensionOverflow => f.write_str("matrix dimensions overflow usize"),
            Self::InvalidMatrixLiteral => {
                f.write_str("matrix element count does not match its dimensions")
            }
        }
    }
}

impl Error for ElaborationError {}

impl From<TypeError> for ElaborationError {
    fn from(value: TypeError) -> Self {
        Self::Type(value)
    }
}

impl From<NaturalEvaluationError> for ElaborationError {
    fn from(value: NaturalEvaluationError) -> Self {
        Self::Natural(value)
    }
}

pub fn elaborate(
    environment: &Environment,
    prepared: &PreparedExpression,
) -> Result<ElaboratedExpression, ElaborationError> {
    let mut expression = deep_clone(&prepared.expression);
    let mut side_conditions = prepared
        .side_conditions
        .iter()
        .map(|condition| {
            Ok(SideCondition {
                introduced_variable: condition.introduced_variable.clone(),
                display_name: condition.display_name.clone(),
                introduced_type: condition.introduced_type.clone(),
                active_ranges: condition.active_ranges.clone(),
                defining_assertions: condition
                    .defining_assertions
                    .iter()
                    .map(deep_clone)
                    .collect(),
                existence: clone_existence(&condition.existence),
            })
        })
        .collect::<Result<Vec<_>, ElaborationError>>()?;
    expand_pointwise_side_conditions(environment, &mut side_conditions)?;

    loop {
        let mut rewrites = 0;

        let mut memberships = MembershipVisitor::new(environment);
        visit_forest(
            &mut memberships,
            prepared.context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += memberships.finish()?;

        let mut diagonals = DiagonalVisitor::new(environment);
        visit_forest(
            &mut diagonals,
            prepared.context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += diagonals.finish()?;

        let mut sequences = SequenceVisitor::new(environment);
        visit_forest(
            &mut sequences,
            prepared.context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += sequences.finish()?;

        let mut leaves = ConcreteLeafVisitor::new(environment);
        visit_forest(
            &mut leaves,
            prepared.context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += leaves.finish()?;

        let mut matrices = MatrixVisitor::new(environment);
        visit_forest(
            &mut matrices,
            prepared.context.clone(),
            &mut expression,
            &mut side_conditions,
        );
        rewrites += matrices.finish()?;

        if rewrites == 0 {
            validate_forest(&expression, &side_conditions)?;
            break;
        }
    }

    Ok(ElaboratedExpression {
        expression,
        side_conditions,
        context: prepared.context.clone(),
    })
}

fn clone_existence(existence: &Existence<TypedMetadata>) -> Existence<TypedMetadata> {
    match existence {
        Existence::Guaranteed => Existence::Guaranteed,
        Existence::Checkable(assertions) => {
            Existence::Checkable(assertions.iter().map(deep_clone).collect())
        }
        Existence::Assumed => Existence::Assumed,
    }
}

fn expand_pointwise_side_conditions(
    environment: &Environment,
    conditions: &mut [SideCondition<TypedMetadata>],
) -> Result<(), ElaborationError> {
    for condition in conditions {
        if condition.active_ranges.is_empty() {
            continue;
        }
        let assignments = concrete_range_assignments(environment, &condition.active_ranges)?;
        condition.defining_assertions = assignments
            .iter()
            .flat_map(|assignment| {
                condition
                    .defining_assertions
                    .iter()
                    .map(|assertion| substitute_indices(assertion, assignment))
            })
            .collect();
        if let Existence::Checkable(assertions) = &condition.existence {
            let alternatives = assignments
                .iter()
                .map(|assignment| {
                    boolean_terms(
                        Finop::And,
                        assertions
                            .iter()
                            .map(|assertion| substitute_indices(assertion, assignment))
                            .collect(),
                    )
                })
                .collect::<Vec<_>>();
            condition.existence =
                Existence::Checkable(vec![boolean_terms(Finop::Or, alternatives)]);
        }
        condition.active_ranges.clear();
    }
    Ok(())
}

fn concrete_range_assignments(
    environment: &Environment,
    ranges: &[Range<()>],
) -> Result<Vec<Vec<(Variable, u64)>>, ElaborationError> {
    fn expand(
        environment: &Environment,
        ranges: &[Range<()>],
        index: usize,
        assignment: &mut Vec<(Variable, u64)>,
        result: &mut Vec<Vec<(Variable, u64)>>,
    ) -> Result<(), ElaborationError> {
        let Some(range) = ranges.get(index) else {
            result.push(assignment.clone());
            return Ok(());
        };
        let from = environment.evaluate_natural_with_context(&range.from, assignment, &[])?;
        let to = environment.evaluate_natural_with_context(&range.to, assignment, &[])?;
        if from > to {
            return Err(ElaborationError::InvalidOperands(
                "sequence range must be nonempty",
            ));
        }
        for value in from..=to {
            assignment.push((range.index_variable.clone(), value));
            expand(environment, ranges, index + 1, assignment, result)?;
            assignment.pop();
        }
        Ok(())
    }
    let mut result = Vec::new();
    expand(environment, ranges, 0, &mut Vec::new(), &mut result)?;
    Ok(result)
}

fn substitute_indices(
    expression: &Expr<TypedMetadata>,
    assignment: &[(Variable, u64)],
) -> Expr<TypedMetadata> {
    assignment
        .iter()
        .fold(deep_clone(expression), |result, (variable, value)| {
            substitute_index(&result, variable, *value)
        })
}

fn boolean_terms(op: Finop, mut expressions: Vec<Expr<TypedMetadata>>) -> Expr<TypedMetadata> {
    if expressions.len() == 1 {
        expressions.pop().unwrap()
    } else {
        typed(TypeExpr::Bool, RawExpr::Finop(op, expressions))
    }
}

fn visit_forest<V: VisitMut<TypedMetadata>>(
    visitor: &mut V,
    context: VisitContext,
    expression: &mut Expr<TypedMetadata>,
    side_conditions: &mut [SideCondition<TypedMetadata>],
) {
    visitor.visit_expr_mut(context.clone(), expression);
    for condition in side_conditions {
        for assertion in &mut condition.defining_assertions {
            visitor.visit_expr_mut(context.clone(), assertion);
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                visitor.visit_expr_mut(context.clone(), assertion);
            }
        }
    }
}

fn typed(ty: TypeExpr<()>, raw: RawExpr<TypedMetadata>) -> Expr<TypedMetadata> {
    Expr::with_metadata(TypedMetadata::resolved(ty), raw)
}

fn natural(value: u64) -> Expr<TypedMetadata> {
    typed(TypeExpr::Nat, RawExpr::NatLiteral(value))
}

fn real(value: u64) -> Expr<TypedMetadata> {
    typed(TypeExpr::Real, RawExpr::NatLiteral(value))
}

fn boolean(value: bool) -> Expr<TypedMetadata> {
    typed(
        TypeExpr::Bool,
        RawExpr::CmpChain(CmpChain {
            start: natural(0),
            assertions: vec![(if value { Cmp::Eq } else { Cmp::Ne }, natural(0))],
        }),
    )
}

fn comparison(
    left: Expr<TypedMetadata>,
    comparison: Cmp,
    right: Expr<TypedMetadata>,
) -> Expr<TypedMetadata> {
    typed(
        TypeExpr::Bool,
        RawExpr::CmpChain(CmpChain {
            start: left,
            assertions: vec![(comparison, right)],
        }),
    )
}

fn symbolic_type(expression: &Expr<TypedMetadata>) -> Result<TypeExpr<()>, ElaborationError> {
    expression.meta.get_type().map_err(Into::into)
}

fn matrix_dimensions<Metadata>(
    environment: &Environment,
    ty: &TypeExpr<Metadata>,
) -> Result<Option<(u64, u64)>, ElaborationError> {
    match ty {
        TypeExpr::Matrix(rows, cols) => Ok(Some((
            environment.evaluate_natural(rows)?,
            environment.evaluate_natural(cols)?,
        ))),
        _ => Ok(None),
    }
}

fn sequence_parts<'a, Metadata>(
    environment: &Environment,
    ty: &'a TypeExpr<Metadata>,
) -> Result<Option<(&'a TypeExpr<Metadata>, u64)>, ElaborationError> {
    let TypeExpr::Seq(element, length) = ty else {
        return Ok(None);
    };
    let RawExpr::Type(element) = &element.raw else {
        return Err(ElaborationError::InvalidOperands(
            "sequence element must be a type expression",
        ));
    };
    Ok(Some((element, environment.evaluate_natural(length)?)))
}

fn types_equal<A, B>(
    environment: &Environment,
    left: &TypeExpr<A>,
    right: &TypeExpr<B>,
) -> Result<bool, ElaborationError> {
    Ok(match (left, right) {
        (TypeExpr::Bool, TypeExpr::Bool)
        | (TypeExpr::Nat, TypeExpr::Nat)
        | (TypeExpr::Int, TypeExpr::Int)
        | (TypeExpr::Real, TypeExpr::Real) => true,
        (TypeExpr::Matrix(_, _), TypeExpr::Matrix(_, _)) => {
            matrix_dimensions(environment, left)? == matrix_dimensions(environment, right)?
        }
        (TypeExpr::Seq(_, _), TypeExpr::Seq(_, _)) => {
            let Some((left_element, left_length)) = sequence_parts(environment, left)? else {
                unreachable!()
            };
            let Some((right_element, right_length)) = sequence_parts(environment, right)? else {
                unreachable!()
            };
            left_length == right_length && types_equal(environment, left_element, right_element)?
        }
        _ => false,
    })
}

fn matrix_expression(
    rows: usize,
    cols: usize,
    elements: Vec<Expr<TypedMetadata>>,
) -> Result<Expr<TypedMetadata>, ElaborationError> {
    let rows_u64 = u64::try_from(rows).map_err(|_| ElaborationError::DimensionOverflow)?;
    let cols_u64 = u64::try_from(cols).map_err(|_| ElaborationError::DimensionOverflow)?;
    Ok(typed(
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows_u64)),
            Expr::new(RawExpr::NatLiteral(cols_u64)),
        ),
        RawExpr::Matrix(Matrix {
            rows,
            cols,
            elements,
        }),
    ))
}

fn scalar_finop(
    ty: TypeExpr<()>,
    op: Finop,
    expressions: Vec<Expr<TypedMetadata>>,
) -> Expr<TypedMetadata> {
    typed(ty, RawExpr::Finop(op, expressions))
}

struct MembershipVisitor<'a> {
    environment: &'a Environment,
    rewrites: usize,
    error: Option<ElaborationError>,
}

impl<'a> MembershipVisitor<'a> {
    fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            rewrites: 0,
            error: None,
        }
    }

    fn finish(self) -> Result<usize, ElaborationError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }

    fn replacement(
        &self,
        left: &Expr<TypedMetadata>,
        right: &Expr<TypedMetadata>,
        required: bool,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let RawExpr::Type(expected) = &right.raw else {
            return Err(ElaborationError::InvalidOperands(
                "type membership requires a type expression",
            ));
        };
        let actual = symbolic_type(left)?;
        let numeric_real = matches!(expected, TypeExpr::Real)
            && matches!(actual, TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real);
        if !numeric_real && !types_equal(self.environment, &actual, expected)? {
            if required { return Err(ElaborationError::Shape("set membership subject has incompatible domain dimensions or type")); }
            return Ok(boolean(false));
        }
        if matches!(actual, TypeExpr::Nat) {
            return Ok(comparison(deep_clone(left), Cmp::Ge, natural(0)));
        }
        if matches!(actual, TypeExpr::Seq(ref element, _) if matches!(element.raw, RawExpr::Type(TypeExpr::Seq(_, _))))
        {
            return Err(ElaborationError::Unsupported(
                "nested sequence membership is not supported",
            ));
        }
        Ok(boolean(true))
    }
}

impl VisitMut<TypedMetadata> for MembershipVisitor<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let RawExpr::Binop(op @ (Binop::ElementOf | Binop::InDomain), left, right) = &node.raw else {
            return;
        };
        match self.replacement(left, right, matches!(op, Binop::InDomain)) {
            Ok(replacement) => {
                *node = replacement;
                self.rewrites += 1;
            }
            Err(error) => self.error = Some(error),
        }
    }
}

struct SequenceVisitor<'a> {
    environment: &'a Environment,
    rewrites: usize,
    error: Option<ElaborationError>,
}

struct DiagonalVisitor<'a> {
    environment: &'a Environment,
    rewrites: usize,
    error: Option<ElaborationError>,
}

impl<'a> DiagonalVisitor<'a> {
    fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            rewrites: 0,
            error: None,
        }
    }

    fn finish(self) -> Result<usize, ElaborationError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }

    fn diagonal(
        &self,
        operand: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let operand_type = symbolic_type(operand)?;
        let Some((element_type, length)) = sequence_parts(self.environment, &operand_type)? else {
            return Err(ElaborationError::InvalidOperands(
                "diag operand must be a sequence",
            ));
        };
        if !matches!(element_type, TypeExpr::Real) {
            return Err(ElaborationError::InvalidOperands(
                "diag sequence elements must be real scalars",
            ));
        }
        let dimension = usize::try_from(length).map_err(|_| ElaborationError::DimensionOverflow)?;
        if dimension == 0 {
            return Err(ElaborationError::Empty(
                "diag operand sequence must be nonempty",
            ));
        }
        let element_count = dimension
            .checked_mul(dimension)
            .ok_or(ElaborationError::DimensionOverflow)?;
        let sequence_elements = materialize_sequence(self.environment, operand)?;
        if sequence_elements.len() != dimension {
            return Err(ElaborationError::InvalidOperands(
                "materialized sequence length does not match its type",
            ));
        }
        let mut elements = Vec::with_capacity(element_count);
        for (row, diagonal) in sequence_elements.iter().enumerate() {
            for col in 0..dimension {
                elements.push(if row == col {
                    deep_clone(diagonal)
                } else {
                    real(0)
                });
            }
        }
        matrix_expression(dimension, dimension, elements)
    }
}

impl VisitMut<TypedMetadata> for DiagonalVisitor<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let RawExpr::Monop(Monop::Diag, operand) = &node.raw else {
            return;
        };
        match self.diagonal(operand) {
            Ok(replacement) => {
                *node = replacement;
                self.rewrites += 1;
            }
            Err(error) => self.error = Some(error),
        }
    }
}

impl<'a> SequenceVisitor<'a> {
    fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            rewrites: 0,
            error: None,
        }
    }

    fn finish(self) -> Result<usize, ElaborationError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }

    fn subscript(
        &self,
        base: &Expr<TypedMetadata>,
        index: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let RawExpr::Variable(variable) = &base.raw else {
            return Err(ElaborationError::Unsupported(
                "sequence subscript base must be a variable",
            ));
        };
        let symbolic = base.meta.get_type()?;
        let TypeExpr::Seq(element, _) = symbolic else {
            return Err(ElaborationError::InvalidOperands(
                "subscripted variable is not a sequence",
            ));
        };
        let RawExpr::Type(element_type) = &element.raw else {
            return Err(ElaborationError::InvalidOperands(
                "sequence element must be a type expression",
            ));
        };
        let base_type = symbolic_type(base)?;
        let Some((_, length)) = sequence_parts(self.environment, &base_type)? else {
            return Err(ElaborationError::InvalidOperands(
                "subscripted variable is not a sequence",
            ));
        };
        let element_type = open_sequence_element(element_type, &index.with_default_metadata());
        let index = self.environment.evaluate_natural(index)?;
        if index == 0 || index > length {
            return Err(ElaborationError::InvalidOperands(
                "sequence index is outside its one-based bounds",
            ));
        }
        Ok(typed(
            element_type,
            RawExpr::Variable(Variable::new(format!("{}_{{{index}}}", variable.z3_name()))),
        ))
    }

    fn materialized_subscript(
        &self,
        base: &Expr<TypedMetadata>,
        index: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let elements = materialize_sequence(self.environment, base)?;
        let index = self.environment.evaluate_natural(index)?;
        let position = index
            .checked_sub(1)
            .ok_or(ElaborationError::InvalidOperands(
                "sequence index is outside its one-based bounds",
            ))?;
        elements
            .get(usize::try_from(position).map_err(|_| ElaborationError::DimensionOverflow)?)
            .map(deep_clone)
            .ok_or(ElaborationError::InvalidOperands(
                "sequence index is outside its one-based bounds",
            ))
    }

    fn sequence(
        &self,
        op: SeqOp,
        range: &Range<TypedMetadata>,
        body: &Expr<TypedMetadata>,
        result_type: TypeExpr<()>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let from = self.environment.evaluate_natural(&range.from)?;
        let to = self.environment.evaluate_natural(&range.to)?;
        if from > to {
            return Err(ElaborationError::InvalidOperands(
                "sequence range must be nonempty",
            ));
        }
        let terms = (from..=to)
            .map(|index| substitute_index(body, &range.index_variable, index))
            .collect::<Vec<_>>();
        let op = match op {
            SeqOp::Sum => Finop::Plus,
            SeqOp::Prod => Finop::Times,
            SeqOp::BigOr => Finop::Or,
            SeqOp::Map => {
                return Ok(typed(result_type, RawExpr::Finop(Finop::SeqLiteral, terms)));
            }
        };
        Ok(if terms.len() == 1 {
            terms.into_iter().next().unwrap()
        } else {
            scalar_finop(result_type, op, terms)
        })
    }
}

impl VisitMut<TypedMetadata> for SequenceVisitor<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        if let RawExpr::Binop(Binop::SingleSubscript, base, index) = &node.raw
            && matches!(base.raw, RawExpr::Variable(_))
        {
            match self.subscript(base, index) {
                Ok(replacement) => {
                    *node = replacement;
                    self.rewrites += 1;
                }
                Err(error) => self.error = Some(error),
            }
            return;
        }
        if let RawExpr::Seqop(op, range, body) = &node.raw {
            // The body contains a lexical natural variable. Substitute it before
            // recursively elaborating the generated concrete terms.
            let replacement = node
                .meta
                .get_type()
                .map_err(Into::into)
                .and_then(|ty| self.sequence(*op, range, body, ty));
            match replacement {
                Ok(replacement) => {
                    *node = replacement;
                    self.rewrites += 1;
                }
                Err(error) => self.error = Some(error),
            }
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        if let RawExpr::Binop(Binop::SingleSubscript, base, index) = &node.raw {
            let replacement = if matches!(base.raw, RawExpr::Variable(_)) {
                self.subscript(base, index)
            } else {
                self.materialized_subscript(base, index)
            };
            match replacement {
                Ok(replacement) => {
                    *node = replacement;
                    self.rewrites += 1;
                }
                Err(error) => self.error = Some(error),
            }
            return;
        }
        if matches!(node.raw, RawExpr::Variable(_))
            && matches!(node.meta.get_type(), Ok(TypeExpr::Seq(_, _)))
        {
            match materialize_sequence(self.environment, node).map(|elements| {
                typed(
                    node.meta.get_type().unwrap(),
                    RawExpr::Finop(Finop::SeqLiteral, elements),
                )
            }) {
                Ok(replacement) => {
                    *node = replacement;
                    self.rewrites += 1;
                }
                Err(error) => self.error = Some(error),
            }
        }
    }
}

fn materialize_sequence(
    environment: &Environment,
    expression: &Expr<TypedMetadata>,
) -> Result<Vec<Expr<TypedMetadata>>, ElaborationError> {
    let expression_type = symbolic_type(expression)?;
    let Some((element_type, length)) = sequence_parts(environment, &expression_type)? else {
        return Err(ElaborationError::InvalidOperands(
            "expression does not evaluate to a sequence",
        ));
    };
    match &expression.raw {
        RawExpr::Variable(_) => (1..=length)
            .map(|index| {
                Ok(typed(
                    open_sequence_element(element_type, &Expr::new(RawExpr::NatLiteral(index))),
                    RawExpr::Binop(
                        Binop::SingleSubscript,
                        deep_clone(expression),
                        natural(index),
                    ),
                ))
            })
            .collect(),
        RawExpr::Seqop(SeqOp::Map, range, body) => {
            let from = environment.evaluate_natural(&range.from)?;
            let to = environment.evaluate_natural(&range.to)?;
            if from > to {
                return Err(ElaborationError::InvalidOperands(
                    "map range must be nonempty",
                ));
            }
            let elements = (from..=to)
                .map(|index| substitute_index(body, &range.index_variable, index))
                .collect::<Vec<_>>();
            if elements.len()
                != usize::try_from(length).map_err(|_| ElaborationError::DimensionOverflow)?
            {
                return Err(ElaborationError::InvalidOperands(
                    "map range length does not match its sequence type",
                ));
            }
            Ok(elements)
        }
        RawExpr::Finop(Finop::SeqLiteral, elements) => {
            if elements.len()
                != usize::try_from(length).map_err(|_| ElaborationError::DimensionOverflow)?
            {
                return Err(ElaborationError::InvalidOperands(
                    "sequence literal length does not match its type",
                ));
            }
            Ok(elements.iter().map(deep_clone).collect())
        }
        _ => Err(ElaborationError::Unsupported(
            "sequence expression cannot be materialized",
        )),
    }
}

struct ConcreteLeafVisitor<'a> {
    environment: &'a Environment,
    rewrites: usize,
    error: Option<ElaborationError>,
}

impl<'a> ConcreteLeafVisitor<'a> {
    fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            rewrites: 0,
            error: None,
        }
    }

    fn finish(self) -> Result<usize, ElaborationError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }

    fn implicit(&self, dimension: crate::ImplicitDimension) -> Result<u64, ElaborationError> {
        self.environment
            .natural_assignment
            .get(&NaturalParameter::ImplicitDimension(dimension))
            .copied()
            .ok_or_else(|| {
                NaturalEvaluationError::MissingAssignment(NaturalParameter::ImplicitDimension(
                    dimension,
                ))
                .into()
            })
    }

    fn variable(
        &self,
        variable: &Variable,
        ty: &TypeExpr<()>,
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        let Some((rows, cols)) = matrix_dimensions(self.environment, ty)? else {
            return Ok(None);
        };
        let rows = usize::try_from(rows).map_err(|_| ElaborationError::DimensionOverflow)?;
        let cols = usize::try_from(cols).map_err(|_| ElaborationError::DimensionOverflow)?;
        let capacity = rows
            .checked_mul(cols)
            .ok_or(ElaborationError::DimensionOverflow)?;
        let mut elements = Vec::with_capacity(capacity);
        for row in 1..=rows {
            for col in 1..=cols {
                elements.push(typed(
                    TypeExpr::Real,
                    RawExpr::Variable(Variable::new(format!(
                        "{}_{{{row},{col}}}",
                        variable.z3_name()
                    ))),
                ));
            }
        }
        Ok(Some(matrix_expression(rows, cols, elements)?))
    }
}

impl VisitMut<TypedMetadata> for ConcreteLeafVisitor<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let replacement = (|| -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
            Ok(match &node.raw {
                RawExpr::ImplicitDimension(dimension) => Some(natural(self.implicit(*dimension)?)),
                RawExpr::IdentityMatrix { dimension } => {
                    let dimension = usize::try_from(self.implicit(*dimension)?)
                        .map_err(|_| ElaborationError::DimensionOverflow)?;
                    let elements = (0..dimension)
                        .flat_map(|row| (0..dimension).map(move |col| real(u64::from(row == col))))
                        .collect();
                    Some(matrix_expression(dimension, dimension, elements)?)
                }
                RawExpr::StandardBasis { index, dimension } => {
                    let dimension = self.implicit(*dimension)?;
                    let index = self.environment.evaluate_natural(index)?;
                    if index == 0 || index > dimension {
                        return Err(ElaborationError::InvalidOperands(
                            "standard basis index is outside its one-based bounds",
                        ));
                    }
                    let rows = usize::try_from(dimension)
                        .map_err(|_| ElaborationError::DimensionOverflow)?;
                    let elements = (1..=dimension)
                        .map(|row| real(u64::from(row == index)))
                        .collect();
                    Some(matrix_expression(rows, 1, elements)?)
                }
                RawExpr::ZeroMatrix { rows, cols } => {
                    let rows = usize::try_from(self.implicit(*rows)?)
                        .map_err(|_| ElaborationError::DimensionOverflow)?;
                    let cols = usize::try_from(self.implicit(*cols)?)
                        .map_err(|_| ElaborationError::DimensionOverflow)?;
                    let count = rows
                        .checked_mul(cols)
                        .ok_or(ElaborationError::DimensionOverflow)?;
                    Some(matrix_expression(
                        rows,
                        cols,
                        (0..count).map(|_| real(0)).collect(),
                    )?)
                }
                RawExpr::Variable(variable) => match node.meta.get_type() {
                    Ok(ty) => self.variable(variable, &ty)?,
                    Err(_) => None,
                },
                _ => None,
            })
        })();
        match replacement {
            Ok(Some(replacement)) => {
                *node = replacement;
                self.rewrites += 1;
            }
            Ok(None) => {}
            Err(error) => self.error = Some(error),
        }
    }
}

enum Value {
    Scalar(Expr<TypedMetadata>),
    Matrix(Matrix<Expr<TypedMetadata>>),
}

fn clone_matrix(matrix: &Matrix<Expr<TypedMetadata>>) -> Matrix<Expr<TypedMetadata>> {
    Matrix {
        rows: matrix.rows,
        cols: matrix.cols,
        elements: matrix.elements.iter().map(deep_clone).collect(),
    }
}

fn clone_value(value: &Value) -> Value {
    match value {
        Value::Scalar(expression) => Value::Scalar(deep_clone(expression)),
        Value::Matrix(matrix) => Value::Matrix(clone_matrix(matrix)),
    }
}

struct MatrixVisitor<'a> {
    environment: &'a Environment,
    rewrites: usize,
    error: Option<ElaborationError>,
}

impl<'a> MatrixVisitor<'a> {
    fn new(environment: &'a Environment) -> Self {
        Self {
            environment,
            rewrites: 0,
            error: None,
        }
    }

    fn finish(self) -> Result<usize, ElaborationError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }

    fn value(&self, expression: &Expr<TypedMetadata>) -> Result<Value, ElaborationError> {
        match symbolic_type(expression)? {
            TypeExpr::Matrix(_, _) => {
                let RawExpr::Matrix(matrix) = &expression.raw else {
                    return Err(ElaborationError::Unsupported(
                        "matrix expression remains unmaterialized",
                    ));
                };
                Ok(Value::Matrix(clone_matrix(matrix)))
            }
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {
                Ok(Value::Scalar(deep_clone(expression)))
            }
            _ => Err(ElaborationError::InvalidOperands(
                "operation requires numeric operands",
            )),
        }
    }

    fn matrix_operand_pending(
        &self,
        expression: &Expr<TypedMetadata>,
    ) -> Result<bool, ElaborationError> {
        Ok(matches!(symbolic_type(expression)?, TypeExpr::Matrix(_, _))
            && !matches!(expression.raw, RawExpr::Matrix(_)))
    }

    fn node_has_pending_matrix_operand(
        &self,
        node: &Expr<TypedMetadata>,
    ) -> Result<bool, ElaborationError> {
        Ok(match &node.raw {
            RawExpr::Monop(_, inner) => self.matrix_operand_pending(inner)?,
            RawExpr::Binop(Binop::Cast, _, value) => self.matrix_operand_pending(value)?,
            RawExpr::Binop(_, left, right) => {
                self.matrix_operand_pending(left)? || self.matrix_operand_pending(right)?
            }
            RawExpr::Finop(_, expressions) => expressions
                .iter()
                .map(|expression| self.matrix_operand_pending(expression))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .any(|pending| pending),
            RawExpr::CmpChain(chain) => {
                self.matrix_operand_pending(&chain.start)?
                    || chain
                        .assertions
                        .iter()
                        .map(|(_, expression)| self.matrix_operand_pending(expression))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .any(|pending| pending)
            }
            _ => false,
        })
    }

    fn flatten_matrix(
        &self,
        matrix: &Matrix<Expr<TypedMetadata>>,
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        let expected = matrix
            .rows
            .checked_mul(matrix.cols)
            .ok_or(ElaborationError::DimensionOverflow)?;
        if matrix.elements.len() != expected || (matrix.rows == 0) != (matrix.cols == 0) {
            return Err(ElaborationError::InvalidMatrixLiteral);
        }
        if matrix.rows == 0 {
            return Ok(None);
        }
        let blocks = matrix
            .elements
            .iter()
            .map(|element| self.value(element))
            .map(|value| {
                value.map(|value| match value {
                    Value::Scalar(value) => Matrix {
                        rows: 1,
                        cols: 1,
                        elements: vec![value],
                    },
                    Value::Matrix(matrix) => matrix,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if blocks
            .iter()
            .all(|block| block.rows == 1 && block.cols == 1)
        {
            return Ok(None);
        }
        let mut row_heights = Vec::with_capacity(matrix.rows);
        for row in 0..matrix.rows {
            let height = blocks[row * matrix.cols].rows;
            if (1..matrix.cols).any(|col| blocks[row * matrix.cols + col].rows != height) {
                return Err(ElaborationError::Shape(
                    "blocks in a block-matrix row must have equal heights",
                ));
            }
            row_heights.push(height);
        }
        let mut column_widths = Vec::with_capacity(matrix.cols);
        for col in 0..matrix.cols {
            let width = blocks[col].cols;
            if (1..matrix.rows).any(|row| blocks[row * matrix.cols + col].cols != width) {
                return Err(ElaborationError::Shape(
                    "blocks in a block-matrix column must have equal widths",
                ));
            }
            column_widths.push(width);
        }
        let rows = row_heights.iter().try_fold(0usize, |sum, value| {
            sum.checked_add(*value)
                .ok_or(ElaborationError::DimensionOverflow)
        })?;
        let cols = column_widths.iter().try_fold(0usize, |sum, value| {
            sum.checked_add(*value)
                .ok_or(ElaborationError::DimensionOverflow)
        })?;
        let mut elements = Vec::with_capacity(
            rows.checked_mul(cols)
                .ok_or(ElaborationError::DimensionOverflow)?,
        );
        for block_row in 0..matrix.rows {
            for inner_row in 0..row_heights[block_row] {
                for block_col in 0..matrix.cols {
                    let block = &blocks[block_row * matrix.cols + block_col];
                    let start = inner_row * block.cols;
                    elements.extend(
                        block.elements[start..start + block.cols]
                            .iter()
                            .map(deep_clone),
                    );
                }
            }
        }
        Ok(Some(matrix_expression(rows, cols, elements)?))
    }

    fn matrix_negation(
        &self,
        matrix: Matrix<Expr<TypedMetadata>>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        matrix_expression(
            matrix.rows,
            matrix.cols,
            matrix
                .elements
                .into_iter()
                .map(|cell| typed(TypeExpr::Real, RawExpr::Monop(Monop::Neg, cell)))
                .collect(),
        )
    }

    fn transpose(
        &self,
        matrix: Matrix<Expr<TypedMetadata>>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let mut elements = Vec::with_capacity(matrix.elements.len());
        for col in 0..matrix.cols {
            for row in 0..matrix.rows {
                elements.push(deep_clone(&matrix.elements[row * matrix.cols + col]));
            }
        }
        matrix_expression(matrix.cols, matrix.rows, elements)
    }

    fn add_values(&self, left: Value, right: Value) -> Result<Value, ElaborationError> {
        match (left, right) {
            (Value::Scalar(left), Value::Scalar(right)) => Ok(Value::Scalar(scalar_finop(
                scalar_lub_type(&left, &right)?,
                Finop::Plus,
                vec![left, right],
            ))),
            (Value::Matrix(left), Value::Matrix(right)) => {
                if left.rows != right.rows || left.cols != right.cols {
                    return Err(ElaborationError::Shape(
                        "matrix addition requires equal dimensions",
                    ));
                }
                Ok(Value::Matrix(Matrix {
                    rows: left.rows,
                    cols: left.cols,
                    elements: left
                        .elements
                        .into_iter()
                        .zip(right.elements)
                        .map(|(left, right)| {
                            scalar_finop(TypeExpr::Real, Finop::Plus, vec![left, right])
                        })
                        .collect(),
                }))
            }
            _ => Err(ElaborationError::InvalidOperands(
                "scalar-matrix addition is not supported",
            )),
        }
    }

    fn multiply_values(&self, left: Value, right: Value) -> Result<Value, ElaborationError> {
        match (left, right) {
            (Value::Scalar(left), Value::Scalar(right)) => Ok(Value::Scalar(scalar_finop(
                scalar_lub_type(&left, &right)?,
                Finop::Times,
                vec![left, right],
            ))),
            (Value::Scalar(scalar), Value::Matrix(matrix)) => Ok(Value::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|cell| {
                        scalar_finop(
                            TypeExpr::Real,
                            Finop::Times,
                            vec![deep_clone(&scalar), cell],
                        )
                    })
                    .collect(),
            })),
            (Value::Matrix(matrix), Value::Scalar(scalar)) => Ok(Value::Matrix(Matrix {
                rows: matrix.rows,
                cols: matrix.cols,
                elements: matrix
                    .elements
                    .into_iter()
                    .map(|cell| {
                        scalar_finop(
                            TypeExpr::Real,
                            Finop::Times,
                            vec![cell, deep_clone(&scalar)],
                        )
                    })
                    .collect(),
            })),
            (Value::Matrix(left), Value::Matrix(right)) => {
                if left.cols != right.rows {
                    return Err(ElaborationError::Shape(
                        "matrix multiplication requires compatible dimensions",
                    ));
                }
                if left.cols == 0 {
                    return Err(ElaborationError::Empty(
                        "matrix dot product requires at least one term",
                    ));
                }
                let mut elements = Vec::with_capacity(
                    left.rows
                        .checked_mul(right.cols)
                        .ok_or(ElaborationError::DimensionOverflow)?,
                );
                for row in 0..left.rows {
                    for col in 0..right.cols {
                        let terms = (0..left.cols)
                            .map(|inner| {
                                scalar_finop(
                                    TypeExpr::Real,
                                    Finop::Times,
                                    vec![
                                        deep_clone(&left.elements[row * left.cols + inner]),
                                        deep_clone(&right.elements[inner * right.cols + col]),
                                    ],
                                )
                            })
                            .collect();
                        elements.push(scalar_finop(TypeExpr::Real, Finop::Plus, terms));
                    }
                }
                Ok(Value::Matrix(Matrix {
                    rows: left.rows,
                    cols: right.cols,
                    elements,
                }))
            }
        }
    }

    fn value_expression(&self, value: Value) -> Result<Expr<TypedMetadata>, ElaborationError> {
        match value {
            Value::Scalar(expression) => Ok(expression),
            Value::Matrix(matrix) => matrix_expression(matrix.rows, matrix.cols, matrix.elements),
        }
    }

    fn finite(
        &self,
        op: Finop,
        expressions: &[Expr<TypedMetadata>],
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        if expressions.is_empty() {
            return Err(ElaborationError::Empty(match op {
                Finop::Plus => "addition requires at least one operand",
                Finop::Times => "multiplication requires at least one operand",
                _ => return Ok(None),
            }));
        }
        if !matches!(op, Finop::Plus | Finop::Times)
            || expressions
                .iter()
                .all(|expression| !matches!(symbolic_type(expression), Ok(TypeExpr::Matrix(_, _))))
        {
            return Ok(None);
        }
        let mut values = expressions.iter().map(|expression| self.value(expression));
        let first = values.next().unwrap()?;
        let result = values.try_fold(first, |left, right| match op {
            Finop::Plus => self.add_values(left, right?),
            Finop::Times => self.multiply_values(left, right?),
            _ => unreachable!(),
        })?;
        Ok(Some(self.value_expression(result)?))
    }

    fn divide(
        &self,
        left: &Expr<TypedMetadata>,
        right: &Expr<TypedMetadata>,
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        let left = self.value(left)?;
        let right = self.value(right)?;
        if matches!(left, Value::Scalar(_)) && matches!(right, Value::Scalar(_)) {
            return Ok(None);
        }
        let scalar = |value| match value {
            Value::Scalar(value) => Ok(value),
            Value::Matrix(mut matrix)
                if matrix.rows == 1 && matrix.cols == 1 && matrix.elements.len() == 1 =>
            {
                Ok(matrix.elements.pop().unwrap())
            }
            Value::Matrix(_) => Err(ElaborationError::Shape(
                "matrix division is only supported for 1x1 matrices",
            )),
        };
        let left = scalar(left)?;
        let right = scalar(right)?;
        Ok(Some(typed(
            scalar_lub_type(&left, &right)?,
            RawExpr::Binop(Binop::Div, left, right),
        )))
    }

    fn power(
        &self,
        base: &Expr<TypedMetadata>,
        exponent: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let exponent = self.environment.evaluate_natural(exponent)?;
        let base_value = self.value(base)?;
        if let Value::Matrix(matrix) = &base_value
            && matrix.rows != matrix.cols
        {
            return Err(ElaborationError::Shape(
                "matrix power requires a square matrix",
            ));
        }
        if exponent == 0 {
            return match base_value {
                Value::Scalar(base) => Ok(match symbolic_type(&base)? {
                    TypeExpr::Nat => natural(1),
                    TypeExpr::Int => typed(TypeExpr::Int, RawExpr::NatLiteral(1)),
                    TypeExpr::Real => real(1),
                    _ => {
                        return Err(ElaborationError::InvalidOperands(
                            "zero power requires a numeric scalar base",
                        ));
                    }
                }),
                Value::Matrix(matrix) => matrix_identity_like(&matrix),
            };
        }
        let mut result = clone_value(&base_value);
        for _ in 1..exponent {
            result = self.multiply_values(result, clone_value(&base_value))?;
        }
        self.value_expression(result)
    }

    fn cast(
        &self,
        target: &Expr<TypedMetadata>,
        value: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let RawExpr::Type(target) = &target.raw else {
            return Err(ElaborationError::InvalidOperands(
                "cast target must be a type expression",
            ));
        };
        let target: TypeExpr<()> = target.with_default_metadata();
        match (target, self.value(value)?) {
            (TypeExpr::Real, Value::Scalar(value))
                if matches!(symbolic_type(&value)?, TypeExpr::Real) =>
            {
                Ok(value)
            }
            (TypeExpr::Real, Value::Matrix(mut matrix))
                if matrix.rows == 1 && matrix.cols == 1 && matrix.elements.len() == 1 =>
            {
                Ok(matrix.elements.pop().unwrap())
            }
            (TypeExpr::Real, _) => Err(ElaborationError::InvalidOperands(
                "a cast to real requires a real scalar or real-valued 1x1 matrix",
            )),
            (TypeExpr::Matrix(rows, cols), Value::Scalar(value))
                if matches!(symbolic_type(&value)?, TypeExpr::Real) =>
            {
                let rows = self.environment.evaluate_natural(&rows)?;
                let cols = self.environment.evaluate_natural(&cols)?;
                if (rows, cols) == (1, 1) {
                    matrix_expression(1, 1, vec![value])
                } else {
                    Err(ElaborationError::Shape(
                        "a real scalar can only be cast to a 1x1 matrix",
                    ))
                }
            }
            (TypeExpr::Matrix(_, _), Value::Scalar(_)) => Err(ElaborationError::InvalidOperands(
                "a cast to a matrix requires a real scalar",
            )),
            (
                TypeExpr::Set(_)
                | TypeExpr::Bool
                | TypeExpr::Nat
                | TypeExpr::Int
                | TypeExpr::Seq(_, _),
                _,
            ) => Err(ElaborationError::Unsupported(
                "only real and 1x1 matrix casts are supported",
            )),
            (TypeExpr::Matrix(_, _), _) => Err(ElaborationError::InvalidOperands(
                "a cast to a matrix requires a real scalar",
            )),
        }
    }

    fn trace(
        &self,
        expression: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let Value::Matrix(matrix) = self.value(expression)? else {
            return Err(ElaborationError::InvalidOperands("trace requires a matrix"));
        };
        require_nonempty_square(&matrix, "trace")?;
        Ok(scalar_finop(
            TypeExpr::Real,
            Finop::Plus,
            (0..matrix.rows)
                .map(|index| deep_clone(&matrix.elements[index * matrix.cols + index]))
                .collect(),
        ))
    }

    fn determinant(
        &self,
        expression: &Expr<TypedMetadata>,
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let Value::Matrix(matrix) = self.value(expression)? else {
            return Err(ElaborationError::InvalidOperands(
                "determinant requires a matrix",
            ));
        };
        require_nonempty_square(&matrix, "determinant")?;
        determinant_expression(&matrix)
    }

    fn compare_chain(
        &self,
        chain: &CmpChain<TypedMetadata>,
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        if chain.assertions.is_empty() {
            return Err(ElaborationError::Empty(
                "comparison chain requires at least one assertion",
            ));
        }
        let mut previous = &chain.start;
        let mut clauses = Vec::with_capacity(chain.assertions.len());
        let mut changed = false;
        for (op, current) in &chain.assertions {
            let left_type = symbolic_type(previous)?;
            let right_type = symbolic_type(current)?;
            if !matches!(left_type, TypeExpr::Matrix(_, _))
                && !matches!(right_type, TypeExpr::Matrix(_, _))
            {
                clauses.push(comparison(deep_clone(previous), *op, deep_clone(current)));
                previous = current;
                continue;
            }
            changed = true;
            let scalarize = |value| match value {
                Value::Matrix(mut matrix)
                    if matrix.rows == 1 && matrix.cols == 1 && matrix.elements.len() == 1 =>
                {
                    Value::Scalar(matrix.elements.pop().unwrap())
                }
                value => value,
            };
            let left = scalarize(self.value(previous)?);
            let right = scalarize(self.value(current)?);
            let clause = match (left, right) {
                (Value::Scalar(left), Value::Scalar(right)) => comparison(left, *op, right),
                (Value::Matrix(left), Value::Matrix(right)) => {
                    changed = true;
                    if !matches!(op, Cmp::Eq | Cmp::Ne) {
                        return Err(ElaborationError::InvalidOperands(
                            "matrix ordering comparisons are not supported",
                        ));
                    }
                    if left.rows != right.rows || left.cols != right.cols {
                        return Err(ElaborationError::Shape(
                            "matrix equality requires equal dimensions",
                        ));
                    }
                    let cells = left
                        .elements
                        .into_iter()
                        .zip(right.elements)
                        .map(|(left, right)| comparison(left, *op, right))
                        .collect();
                    scalar_finop(
                        TypeExpr::Bool,
                        if matches!(op, Cmp::Eq) {
                            Finop::And
                        } else {
                            Finop::Or
                        },
                        cells,
                    )
                }
                _ => {
                    return Err(ElaborationError::InvalidOperands(
                        "scalar-matrix comparisons are not supported",
                    ));
                }
            };
            clauses.push(clause);
            previous = current;
        }
        if !changed {
            return Ok(None);
        }
        Ok(Some(if clauses.len() == 1 {
            clauses.pop().unwrap()
        } else {
            scalar_finop(TypeExpr::Bool, Finop::And, clauses)
        }))
    }
}

impl VisitMut<TypedMetadata> for MatrixVisitor<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let replacement = (|| -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
            if self.node_has_pending_matrix_operand(node)? {
                return Ok(None);
            }
            match &node.raw {
                RawExpr::Matrix(matrix) => self.flatten_matrix(matrix),
                RawExpr::Monop(Monop::Neg, inner)
                    if matches!(symbolic_type(inner)?, TypeExpr::Matrix(_, _)) =>
                {
                    let Value::Matrix(matrix) = self.value(inner)? else {
                        unreachable!()
                    };
                    Ok(Some(self.matrix_negation(matrix)?))
                }
                RawExpr::Monop(Monop::Transpose, inner) => {
                    let Value::Matrix(matrix) = self.value(inner)? else {
                        return Err(ElaborationError::InvalidOperands(
                            "transpose requires a matrix operand",
                        ));
                    };
                    Ok(Some(self.transpose(matrix)?))
                }
                RawExpr::Monop(Monop::Trace, inner) => Ok(Some(self.trace(inner)?)),
                RawExpr::Monop(Monop::Det, inner) => Ok(Some(self.determinant(inner)?)),
                RawExpr::Binop(Binop::Div, left, right) => self.divide(left, right),
                RawExpr::Binop(Binop::Power, base, exponent) => {
                    Ok(Some(self.power(base, exponent)?))
                }
                RawExpr::Binop(Binop::Cast, target, value) => Ok(Some(self.cast(target, value)?)),
                RawExpr::Finop(op @ (Finop::Plus | Finop::Times), expressions) => {
                    self.finite(*op, expressions)
                }
                RawExpr::CmpChain(chain) => self.compare_chain(chain),
                _ => Ok(None),
            }
        })();
        match replacement {
            Ok(Some(replacement)) => {
                *node = replacement;
                self.rewrites += 1;
            }
            Ok(None) => {}
            Err(error) => self.error = Some(error),
        }
    }
}

fn scalar_lub_type(
    left: &Expr<TypedMetadata>,
    right: &Expr<TypedMetadata>,
) -> Result<TypeExpr<()>, ElaborationError> {
    let left = left.meta.get_type()?;
    let right = right.meta.get_type()?;
    Ok(match (left, right) {
        (TypeExpr::Nat, TypeExpr::Nat) => TypeExpr::Nat,
        (TypeExpr::Nat | TypeExpr::Int, TypeExpr::Nat | TypeExpr::Int) => TypeExpr::Int,
        (
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
        ) => TypeExpr::Real,
        _ => {
            return Err(ElaborationError::InvalidOperands(
                "operation requires numeric scalar operands",
            ));
        }
    })
}

fn require_nonempty_square(
    matrix: &Matrix<Expr<TypedMetadata>>,
    operation: &'static str,
) -> Result<(), ElaborationError> {
    if matrix.rows == 0 {
        return Err(ElaborationError::Empty(match operation {
            "trace" => "trace requires a nonempty matrix",
            _ => "determinant requires a nonempty matrix",
        }));
    }
    if matrix.rows != matrix.cols {
        return Err(ElaborationError::Shape(match operation {
            "trace" => "trace requires a square matrix",
            _ => "determinant requires a square matrix",
        }));
    }
    Ok(())
}

fn determinant_expression(
    matrix: &Matrix<Expr<TypedMetadata>>,
) -> Result<Expr<TypedMetadata>, ElaborationError> {
    if matrix.rows == 1 {
        return Ok(deep_clone(&matrix.elements[0]));
    }
    let mut terms = Vec::with_capacity(matrix.cols);
    for col in 0..matrix.cols {
        let mut minor = Vec::with_capacity((matrix.rows - 1) * (matrix.cols - 1));
        for row in 1..matrix.rows {
            for minor_col in 0..matrix.cols {
                if minor_col != col {
                    minor.push(deep_clone(&matrix.elements[row * matrix.cols + minor_col]));
                }
            }
        }
        let determinant = determinant_expression(&Matrix {
            rows: matrix.rows - 1,
            cols: matrix.cols - 1,
            elements: minor,
        })?;
        let term = scalar_finop(
            TypeExpr::Real,
            Finop::Times,
            vec![deep_clone(&matrix.elements[col]), determinant],
        );
        terms.push(if col % 2 == 0 {
            term
        } else {
            typed(TypeExpr::Real, RawExpr::Monop(Monop::Neg, term))
        });
    }
    Ok(scalar_finop(TypeExpr::Real, Finop::Plus, terms))
}

fn matrix_identity_like(
    matrix: &Matrix<Expr<TypedMetadata>>,
) -> Result<Expr<TypedMetadata>, ElaborationError> {
    let real_cells = matrix
        .elements
        .iter()
        .any(|cell| matches!(cell.meta.get_type(), Ok(TypeExpr::Real)));
    matrix_expression(
        matrix.rows,
        matrix.cols,
        (0..matrix.rows)
            .flat_map(|row| {
                (0..matrix.cols).map(move |col| {
                    if real_cells {
                        real(u64::from(row == col))
                    } else {
                        natural(u64::from(row == col))
                    }
                })
            })
            .collect(),
    )
}

fn substitute_index(
    expression: &Expr<TypedMetadata>,
    variable: &Variable,
    value: u64,
) -> Expr<TypedMetadata> {
    let recurse = |expression: &Expr<TypedMetadata>| substitute_index(expression, variable, value);
    let raw = match &expression.raw {
        RawExpr::SetComprehension {
            variable: binder,
            domain,
            predicate,
        } => RawExpr::SetComprehension {
            variable: binder.clone(),
            domain: substitute_type(domain, variable, value),
            predicate: if binder == variable {
                deep_clone(predicate)
            } else {
                recurse(predicate)
            },
        },
        RawExpr::Variable(found) if found == variable => RawExpr::NatLiteral(value),
        RawExpr::BoolLiteral(value) => RawExpr::BoolLiteral(*value),
        RawExpr::EmptySet => RawExpr::EmptySet,
        RawExpr::Hole => RawExpr::Hole,
        RawExpr::Ellipsis => RawExpr::Ellipsis,
        RawExpr::ImplicitDimension(dimension) => RawExpr::ImplicitDimension(*dimension),
        RawExpr::BoundNatural(index) => RawExpr::BoundNatural(*index),
        RawExpr::IdentityMatrix { dimension } => RawExpr::IdentityMatrix {
            dimension: *dimension,
        },
        RawExpr::StandardBasis { index, dimension } => RawExpr::StandardBasis {
            index: recurse(index),
            dimension: *dimension,
        },
        RawExpr::ZeroMatrix { rows, cols } => RawExpr::ZeroMatrix {
            rows: *rows,
            cols: *cols,
        },
        RawExpr::Type(ty) => RawExpr::Type(substitute_type(ty, variable, value)),
        RawExpr::Variable(found) => RawExpr::Variable(found.clone()),
        RawExpr::NatLiteral(value) => RawExpr::NatLiteral(*value),
        RawExpr::Matrix(matrix) => RawExpr::Matrix(Matrix {
            rows: matrix.rows,
            cols: matrix.cols,
            elements: matrix.elements.iter().map(recurse).collect(),
        }),
        RawExpr::Monop(op, inner) => RawExpr::Monop(*op, recurse(inner)),
        RawExpr::Binop(op, left, right) => RawExpr::Binop(*op, recurse(left), recurse(right)),
        RawExpr::Triop(op, first, second, third) => {
            RawExpr::Triop(*op, recurse(first), recurse(second), recurse(third))
        }
        RawExpr::Finop(op, expressions) => {
            RawExpr::Finop(*op, expressions.iter().map(recurse).collect())
        }
        RawExpr::CmpChain(chain) => RawExpr::CmpChain(CmpChain {
            start: recurse(&chain.start),
            assertions: chain
                .assertions
                .iter()
                .map(|(op, expression)| (*op, recurse(expression)))
                .collect(),
        }),
        RawExpr::LogicChain(chain) => RawExpr::LogicChain(LogicChain {
            start: recurse(&chain.start),
            assertions: chain
                .assertions
                .iter()
                .map(|(op, expression)| (*op, recurse(expression)))
                .collect(),
        }),
        RawExpr::Seqop(op, range, body) => RawExpr::Seqop(
            *op,
            Range {
                index_variable: range.index_variable.clone(),
                from: recurse(&range.from),
                to: recurse(&range.to),
            },
            if range.index_variable == *variable {
                deep_clone(body)
            } else {
                recurse(body)
            },
        ),
    };
    let metadata = expression
        .meta
        .get_type()
        .map(|ty| {
            TypedMetadata::resolved(substitute_type_variable(
                &ty,
                variable,
                &Expr::new(RawExpr::NatLiteral(value)),
            ))
        })
        .unwrap_or_else(|_| expression.meta.clone());
    Expr::with_metadata(metadata, raw)
}

fn substitute_type(
    ty: &TypeExpr<TypedMetadata>,
    variable: &Variable,
    value: u64,
) -> TypeExpr<TypedMetadata> {
    match ty {
        TypeExpr::Set(element) => {
            TypeExpr::Set(Box::new(substitute_type(element, variable, value)))
        }
        TypeExpr::Bool => TypeExpr::Bool,
        TypeExpr::Nat => TypeExpr::Nat,
        TypeExpr::Int => TypeExpr::Int,
        TypeExpr::Real => TypeExpr::Real,
        TypeExpr::Matrix(rows, cols) => TypeExpr::Matrix(
            substitute_index(rows, variable, value),
            substitute_index(cols, variable, value),
        ),
        TypeExpr::Seq(element, size) => TypeExpr::Seq(
            substitute_index(element, variable, value),
            substitute_index(size, variable, value),
        ),
    }
}

fn validate_forest(
    expression: &Expr<TypedMetadata>,
    side_conditions: &[SideCondition<TypedMetadata>],
) -> Result<(), ElaborationError> {
    let mut validator = CoreValidator { error: None };
    validator.visit_expr(expression);
    for condition in side_conditions {
        for assertion in &condition.defining_assertions {
            validator.visit_expr(assertion);
        }
        if let Existence::Checkable(assertions) = &condition.existence {
            for assertion in assertions {
                validator.visit_expr(assertion);
            }
        }
    }
    validator.error.map_or(Ok(()), Err)
}

struct CoreValidator {
    error: Option<ElaborationError>,
}

impl Visit<TypedMetadata> for CoreValidator {
    fn visit_expr(&mut self, node: &Expr<TypedMetadata>) {
        if self.error.is_some() {
            return;
        }
        visit::visit_expr(self, node);
        if self.error.is_some() {
            return;
        }
        if node
            .meta
            .get_type()
            .is_ok_and(|ty| contains_unbound_natural(&ty))
        {
            self.error = Some(ElaborationError::Unsupported(
                "unbound natural type index remains after concrete elaboration",
            ));
            return;
        }
        self.error = match &node.raw {
            RawExpr::SetComprehension { .. } => Some(ElaborationError::Unsupported(
                "set values must be eliminated before Z3 lowering",
            )),
            RawExpr::Hole => Some(ElaborationError::Unsupported(
                "holes are not supported by to_z3",
            )),
            RawExpr::Ellipsis => Some(ElaborationError::Unsupported(
                "ellipses must be eliminated before Z3 lowering",
            )),
            RawExpr::ImplicitDimension(_)
            | RawExpr::BoundNatural(_)
            | RawExpr::IdentityMatrix { .. }
            | RawExpr::StandardBasis { .. }
            | RawExpr::ZeroMatrix { .. }
            | RawExpr::Seqop(_, _, _)
            | RawExpr::Triop(_, _, _, _) => Some(ElaborationError::Unsupported(
                "expression remains after concrete elaboration",
            )),
            RawExpr::Type(_) => Some(ElaborationError::Unsupported(
                "type expressions are not supported by to_z3",
            )),
            RawExpr::Monop(op, _) if !matches!(op, Monop::Neg | Monop::Not) => Some(
                ElaborationError::Unsupported("unary operator remains after concrete elaboration"),
            ),
            RawExpr::Binop(op, _, _) if !matches!(op, Binop::Div) => Some(
                ElaborationError::Unsupported("binary operator remains after concrete elaboration"),
            ),
            RawExpr::Finop(op, _)
                if !matches!(
                    op,
                    Finop::Plus | Finop::Times | Finop::And | Finop::Or | Finop::SeqLiteral
                ) =>
            {
                Some(ElaborationError::Unsupported(
                    "finite operator remains after concrete elaboration",
                ))
            }
            RawExpr::Variable(_)
                if matches!(
                    node.meta.get_type(),
                    Ok(TypeExpr::Matrix(_, _) | TypeExpr::Seq(_, _))
                ) =>
            {
                Some(ElaborationError::Unsupported(
                    "non-scalar variable remains after concrete elaboration",
                ))
            }
            RawExpr::Matrix(matrix)
                if matrix.elements.iter().any(|cell| {
                    matches!(
                        cell.meta.get_type(),
                        Ok(TypeExpr::Matrix(_, _) | TypeExpr::Seq(_, _) | TypeExpr::Bool)
                    )
                }) =>
            {
                Some(ElaborationError::InvalidOperands(
                    "flat matrix cells must be numeric scalars",
                ))
            }
            RawExpr::LogicChain(chain)
                if !matches!(chain.assertions.as_slice(), [] | [(Logic::Imp, _)]) =>
            {
                Some(ElaborationError::Unsupported(
                    "logic chain remains after preprocessing",
                ))
            }
            _ => None,
        };
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ratex_parser::parse;

    use super::{DiagonalVisitor, ElaborationError, elaborate};
    use crate::{
        Environment, Expr, Finop, Matrix, NaturalParameter, RawExpr, TypeExpr,
        enumerable_envspec::infer_symbolic_type_environment,
        from_tex,
        preprocessing::prepare_expression,
        type_resolver::TypedMetadata,
        visit::{self, Visit},
        visit_mut::VisitContext,
    };

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
        active_ranges: Vec::new(),
    };

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
    }

    fn matrix_type(rows: u64, cols: u64) -> TypeExpr<()> {
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows)),
            Expr::new(RawExpr::NatLiteral(cols)),
        )
    }

    fn prepare(
        tex: &str,
        assumptions: &[&str],
    ) -> (
        crate::preprocessing::PreparedExpression,
        crate::type_resolver::SymbolicTypeEnvironment,
    ) {
        let assumptions = assumptions
            .iter()
            .map(|assumption| expression(assumption))
            .collect::<Vec<_>>();
        let types = infer_symbolic_type_environment(&assumptions).unwrap();
        let prepared = prepare_expression(&types, &expression(tex), POSITIVE).unwrap();
        (prepared, types)
    }

    #[test]
    fn matrix_arithmetic_becomes_a_flat_scalar_cell_matrix() {
        let (prepared, _) = prepare(
            "A B + C",
            &[
                r"A \in \mathbb{R}^{2 \times 2}",
                r"B \in \mathbb{R}^{2 \times 2}",
                r"C \in \mathbb{R}^{2 \times 2}",
            ],
        );
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let RawExpr::Matrix(matrix) = &elaborated.expression.raw else {
            panic!("matrix arithmetic was not elaborated to a matrix value")
        };
        assert_eq!((matrix.rows, matrix.cols, matrix.elements.len()), (2, 2, 4));
        assert!(matrix.elements.iter().all(|cell| {
            matches!(cell.raw, RawExpr::Finop(Finop::Plus, _))
                && !matches!(cell.raw, RawExpr::Matrix(_))
        }));
    }

    #[test]
    fn sequence_ranges_are_specialized_from_the_natural_assignment() {
        let (prepared, _) = prepare(
            r"\sum_{i=1}^{n} z_i",
            &[r"z \in \operatorname{Seq}_{n}(\mathbb{R})"],
        );
        let environment = Environment {
            natural_assignment: HashMap::from([(
                NaturalParameter::Variable(crate::Variable::new("n")),
                2,
            )]),
        };
        let elaborated = elaborate(&environment, &prepared).unwrap();
        let RawExpr::Finop(Finop::Plus, terms) = &elaborated.expression.raw else {
            panic!("sequence sum was not expanded")
        };
        assert_eq!(terms.len(), 2);
        assert_eq!(terms[0].as_latex().to_string(), "z_{1}");
        assert_eq!(terms[1].as_latex().to_string(), "z_{2}");
    }

    #[test]
    fn sequence_sums_do_not_require_sequence_access() {
        let (prepared, _) = prepare(r"\sum_{i=0}^{2}i", &[]);
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let RawExpr::Finop(Finop::Plus, terms) = &elaborated.expression.raw else {
            panic!("sequence sum was not expanded")
        };
        assert_eq!(
            terms
                .iter()
                .map(|term| term.as_latex().to_string())
                .collect::<Vec<_>>(),
            ["0", "1", "2"]
        );
    }

    #[test]
    fn diagonalization_materializes_exactly_the_selected_sequence_elements() {
        for dimension in 1..=3 {
            let assumption = format!(r"z \in \operatorname{{Seq}}_{{{dimension}}}(\mathbb{{R}})");
            let (prepared, _) = prepare(r"\operatorname{diag}(z)", &[&assumption]);
            let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
            let RawExpr::Matrix(matrix) = &elaborated.expression.raw else {
                panic!("diag was not elaborated to a matrix")
            };
            assert_eq!((matrix.rows, matrix.cols), (dimension, dimension));
            for row in 0..dimension {
                for col in 0..dimension {
                    let rendered = matrix.elements[row * dimension + col]
                        .as_latex()
                        .to_string();
                    if row == col {
                        assert_eq!(rendered, format!("z_{{{}}}", row + 1));
                    } else {
                        assert_eq!(rendered, "0");
                    }
                }
            }
        }
    }

    #[test]
    fn diagonalization_materializes_mapped_square_roots() {
        let (prepared, _) = prepare(
            r"\operatorname{diag}(\operatorname{map}_{i=1}^{2}\lambda_i^{\frac{1}{2}})",
            &[r"\lambda \in \operatorname{Seq}_{2}(\mathbb{R})"],
        );
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let RawExpr::Matrix(matrix) = &elaborated.expression.raw else {
            panic!("mapped diagonal was not elaborated")
        };
        assert_eq!((matrix.rows, matrix.cols), (2, 2));
        assert_eq!(matrix.elements[1].as_latex().to_string(), "0");
        assert_eq!(matrix.elements[2].as_latex().to_string(), "0");
        assert_ne!(
            matrix.elements[0].as_latex().to_string(),
            matrix.elements[3].as_latex().to_string()
        );
        let [condition] = elaborated.side_conditions.as_slice() else {
            panic!("expected one pointwise root condition")
        };
        assert!(condition.active_ranges.is_empty());
        assert_eq!(condition.defining_assertions.len(), 4);
        let crate::visit_mut::Existence::Checkable(assertions) = &condition.existence else {
            panic!("scalar roots should retain a checkable existence condition")
        };
        assert_eq!(assertions.len(), 1);
        assert!(matches!(assertions[0].raw, RawExpr::Finop(Finop::Or, _)));
    }

    #[test]
    fn diagonalization_rejects_nonvariable_and_empty_sequences() {
        let sequence_type = |length| {
            TypeExpr::Seq(
                Expr::new(RawExpr::Type(TypeExpr::Real)),
                Expr::new(RawExpr::NatLiteral(length)),
            )
        };
        let nonvariable = Expr::with_metadata(
            TypedMetadata::resolved(sequence_type(1)),
            RawExpr::Matrix(Matrix {
                rows: 1,
                cols: 1,
                elements: vec![Expr::with_metadata(
                    TypedMetadata::resolved(TypeExpr::Real),
                    RawExpr::NatLiteral(1),
                )],
            }),
        );
        let empty = Expr::with_metadata(
            TypedMetadata::resolved(sequence_type(0)),
            RawExpr::Variable(crate::Variable::new("z")),
        );
        let environment = Environment::default();
        let visitor = DiagonalVisitor::new(&environment);
        assert_eq!(
            visitor.diagonal(&nonvariable),
            Err(ElaborationError::Unsupported(
                "sequence expression cannot be materialized"
            ))
        );
        assert_eq!(
            visitor.diagonal(&empty),
            Err(ElaborationError::Empty(
                "diag operand sequence must be nonempty"
            ))
        );
    }

    #[test]
    fn standalone_map_elaborates_to_a_sequence_literal() {
        let (prepared, _) = prepare(r"\operatorname{map}_{i=0}^{2}i", &[]);
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let RawExpr::Finop(Finop::SeqLiteral, elements) = &elaborated.expression.raw else {
            panic!("standalone map should elaborate to a sequence literal")
        };
        assert_eq!(
            elements
                .iter()
                .map(|element| element.as_latex().to_string())
                .collect::<Vec<_>>(),
            ["0", "1", "2"]
        );
    }

    #[test]
    fn sequence_literals_support_subscripts_and_diagonalization() {
        let (prepared, _) = prepare(r"\left(1, 2, 3\right)_2", &[]);
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        assert_eq!(elaborated.expression.as_latex().to_string(), "2");

        let (prepared, _) = prepare(
            r"\operatorname{diag}(a, b)",
            &[r"a \in \mathbb{R}", r"b \in \mathbb{R}"],
        );
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let RawExpr::Matrix(matrix) = &elaborated.expression.raw else {
            panic!("diag of a sequence literal should elaborate to a matrix")
        };
        assert_eq!(
            matrix
                .elements
                .iter()
                .map(|element| element.as_latex().to_string())
                .collect::<Vec<_>>(),
            ["a", "0", "0", "b"]
        );
    }

    #[test]
    fn side_condition_types_remain_symbolic_while_definitions_are_elaborated() {
        let (prepared, _) = prepare(r"A^{\frac{1}{2}}", &[r"A \in \mathbb{R}^{2 \times 2}"]);
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let [condition] = elaborated.side_conditions.as_slice() else {
            panic!("expected one square-root side condition")
        };
        assert_eq!(condition.introduced_type, matrix_type(2, 2));
        struct PowerFinder(bool);
        impl Visit<crate::type_resolver::TypedMetadata> for PowerFinder {
            fn visit_raw_expr_binop(
                &mut self,
                op: &crate::Binop,
                left: &Expr<crate::type_resolver::TypedMetadata>,
                right: &Expr<crate::type_resolver::TypedMetadata>,
            ) {
                self.0 |= matches!(op, crate::Binop::Power);
                visit::visit_raw_expr_binop(self, op, left, right);
            }
        }
        let mut powers = PowerFinder(false);
        for assertion in &condition.defining_assertions {
            powers.visit_expr(assertion);
        }
        assert!(!powers.0);
    }

    #[test]
    fn triangular_ranges_expand_pointwise_side_conditions_exactly() {
        let (prepared, _) = prepare(
            r"\sum_{i=1}^{n}\sum_{j=1}^{i}\left(x + i + j\right)^{\frac{1}{2}}",
            &[r"x \in \mathbb{R}", r"n \in \mathbb{N}"],
        );
        let environment = Environment {
            natural_assignment: HashMap::from([(
                NaturalParameter::Variable(crate::Variable::new("n")),
                2,
            )]),
        };
        let elaborated = elaborate(&environment, &prepared).unwrap();
        let [condition] = elaborated.side_conditions.as_slice() else {
            panic!("expected one lifted root condition")
        };
        assert!(condition.active_ranges.is_empty());
        assert_eq!(condition.defining_assertions.len(), 6);
    }

    #[test]
    fn concrete_shape_errors_are_reported_before_z3_construction() {
        let (prepared, _) = prepare(
            "A B",
            &[
                r"A \in \mathbb{R}^{2 \times 2}",
                r"B \in \mathbb{R}^{1 \times 2}",
            ],
        );
        assert!(matches!(
            elaborate(&Environment::default(), &prepared),
            Err(ElaborationError::Shape(
                "matrix multiplication requires compatible dimensions"
            ))
        ));
    }
}
