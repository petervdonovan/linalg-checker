//! Environment-specific elaboration of symbolically typed expressions.
//!
//! This phase runs after environment enumeration. It specializes symbolic
//! dimensions and removes operations whose meaning depends on concrete matrix
//! or sequence sizes, leaving only scalar operations and flat matrix values.

use std::{error::Error, fmt};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Logic, LogicChain, Matrix, Monop,
    NaturalEvaluationError, NaturalParameter, Range, RawExpr, SeqOp, Type, TypeExpr, Variable,
    deep_clone::deep_clone,
    preprocessing::PreparedExpression,
    type_resolver::{MaybeTyped, TypeError, TypedMetadata},
    visit::{self, Visit},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Clone, Debug)]
pub struct ElaboratedExpression {
    pub expression: Expr<TypedMetadata>,
    pub side_conditions: Vec<SideCondition<TypedMetadata, Type>>,
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
                introduced_type: condition.introduced_type.concretize(environment)?,
                defining_assertions: condition
                    .defining_assertions
                    .iter()
                    .map(deep_clone)
                    .collect(),
                existence: clone_existence(&condition.existence),
            })
        })
        .collect::<Result<Vec<_>, ElaborationError>>()?;

    loop {
        let mut rewrites = 0;

        let mut memberships = MembershipVisitor::new(environment);
        visit_forest(
            &mut memberships,
            prepared.context,
            &mut expression,
            &mut side_conditions,
        );
        rewrites += memberships.finish()?;

        let mut diagonals = DiagonalVisitor::new(environment);
        visit_forest(
            &mut diagonals,
            prepared.context,
            &mut expression,
            &mut side_conditions,
        );
        rewrites += diagonals.finish()?;

        let mut sequences = SequenceVisitor::new(environment);
        visit_forest(
            &mut sequences,
            prepared.context,
            &mut expression,
            &mut side_conditions,
        );
        rewrites += sequences.finish()?;

        let mut leaves = ConcreteLeafVisitor::new(environment);
        visit_forest(
            &mut leaves,
            prepared.context,
            &mut expression,
            &mut side_conditions,
        );
        rewrites += leaves.finish()?;

        let mut matrices = MatrixVisitor::new(environment);
        visit_forest(
            &mut matrices,
            prepared.context,
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
        context: prepared.context,
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

fn visit_forest<V: VisitMut<TypedMetadata>, IntroducedType>(
    visitor: &mut V,
    context: VisitContext,
    expression: &mut Expr<TypedMetadata>,
    side_conditions: &mut [SideCondition<TypedMetadata, IntroducedType>],
) {
    visitor.visit_expr_mut(context, expression);
    for condition in side_conditions {
        for assertion in &mut condition.defining_assertions {
            visitor.visit_expr_mut(context, assertion);
        }
        if let Existence::Checkable(assertions) = &mut condition.existence {
            for assertion in assertions {
                visitor.visit_expr_mut(context, assertion);
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

fn concrete_type(
    environment: &Environment,
    expression: &Expr<TypedMetadata>,
) -> Result<Type, ElaborationError> {
    Ok(expression.meta.get_type()?.concretize(environment)?)
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
    ) -> Result<Expr<TypedMetadata>, ElaborationError> {
        let RawExpr::Variable(_) = &left.raw else {
            return Err(ElaborationError::InvalidOperands(
                "type membership requires a variable subject",
            ));
        };
        let RawExpr::Type(expected) = &right.raw else {
            return Err(ElaborationError::InvalidOperands(
                "type membership requires a type expression",
            ));
        };
        let actual = concrete_type(self.environment, left)?;
        let expected = expected.concretize(self.environment)?;
        if actual != expected {
            return Ok(boolean(false));
        }
        if matches!(actual, Type::Nat) {
            return Ok(comparison(deep_clone(left), Cmp::Ge, natural(0)));
        }
        if matches!(actual, Type::Seq(ref sequence) if matches!(sequence.t, Type::Seq(_))) {
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
        let RawExpr::Binop(Binop::ElementOf, left, right) = &node.raw else {
            return;
        };
        match self.replacement(left, right) {
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
        if !matches!(operand.raw, RawExpr::Variable(_)) {
            return Err(ElaborationError::Unsupported(
                "diag operand must be a sequence variable",
            ));
        }
        let Type::Seq(sequence) = concrete_type(self.environment, operand)? else {
            return Err(ElaborationError::InvalidOperands(
                "diag operand must be a sequence",
            ));
        };
        if sequence.t != Type::Real {
            return Err(ElaborationError::InvalidOperands(
                "diag sequence elements must be real scalars",
            ));
        }
        let dimension =
            usize::try_from(sequence.n).map_err(|_| ElaborationError::DimensionOverflow)?;
        if dimension == 0 {
            return Err(ElaborationError::Empty(
                "diag operand sequence must be nonempty",
            ));
        }
        let element_count = dimension
            .checked_mul(dimension)
            .ok_or(ElaborationError::DimensionOverflow)?;
        let mut elements = Vec::with_capacity(element_count);
        for row in 0..dimension {
            for col in 0..dimension {
                elements.push(if row == col {
                    typed(
                        TypeExpr::Real,
                        RawExpr::Binop(
                            Binop::SingleSubscript,
                            deep_clone(operand),
                            natural(
                                u64::try_from(row + 1)
                                    .map_err(|_| ElaborationError::DimensionOverflow)?,
                            ),
                        ),
                    )
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
        let Type::Seq(sequence) = concrete_type(self.environment, base)? else {
            return Err(ElaborationError::InvalidOperands(
                "subscripted variable is not a sequence",
            ));
        };
        let index = self.environment.evaluate_natural(index)?;
        if index == 0 || index > sequence.n {
            return Err(ElaborationError::InvalidOperands(
                "sequence index is outside its one-based bounds",
            ));
        }
        Ok(typed(
            element_type.with_default_metadata(),
            RawExpr::Variable(Variable::new(format!("{}_{{{index}}}", variable.z3_name()))),
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
        if from == 0 || from > to {
            return Err(ElaborationError::InvalidOperands(
                "sequence range must be nonempty and one-based",
            ));
        }
        let terms = (from..=to)
            .map(|index| substitute_index(body, &range.index_variable, index))
            .collect::<Vec<_>>();
        let op = match op {
            SeqOp::Sum => Finop::Plus,
            SeqOp::Prod => Finop::Times,
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
        let replacement = match &node.raw {
            RawExpr::Binop(Binop::SingleSubscript, base, index) => {
                Some(self.subscript(base, index))
            }
            _ => None,
        };
        if let Some(replacement) = replacement {
            match replacement {
                Ok(replacement) => {
                    *node = replacement;
                    self.rewrites += 1;
                }
                Err(error) => self.error = Some(error),
            }
        }
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
        ty: Type,
    ) -> Result<Option<Expr<TypedMetadata>>, ElaborationError> {
        let Type::Matrix(rows, cols) = ty else {
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
                    Ok(ty) => self.variable(variable, ty.concretize(self.environment)?)?,
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
        match concrete_type(self.environment, expression)? {
            Type::Matrix(_, _) => {
                let RawExpr::Matrix(matrix) = &expression.raw else {
                    return Err(ElaborationError::Unsupported(
                        "matrix expression remains unmaterialized",
                    ));
                };
                Ok(Value::Matrix(clone_matrix(matrix)))
            }
            Type::Nat | Type::Int | Type::Real => Ok(Value::Scalar(deep_clone(expression))),
            _ => Err(ElaborationError::InvalidOperands(
                "operation requires numeric operands",
            )),
        }
    }

    fn matrix_operand_pending(
        &self,
        expression: &Expr<TypedMetadata>,
    ) -> Result<bool, ElaborationError> {
        Ok(matches!(
            concrete_type(self.environment, expression)?,
            Type::Matrix(_, _)
        ) && !matches!(expression.raw, RawExpr::Matrix(_)))
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
            || expressions.iter().all(|expression| {
                !matches!(
                    concrete_type(self.environment, expression),
                    Ok(Type::Matrix(_, _))
                )
            })
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
                Value::Scalar(base) => Ok(match concrete_type(self.environment, &base)? {
                    Type::Nat => natural(1),
                    Type::Int => typed(TypeExpr::Int, RawExpr::NatLiteral(1)),
                    Type::Real => real(1),
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
        let target = target.concretize(self.environment)?;
        match (target, self.value(value)?) {
            (Type::Real, Value::Scalar(value))
                if matches!(concrete_type(self.environment, &value)?, Type::Real) =>
            {
                Ok(value)
            }
            (Type::Real, Value::Matrix(mut matrix))
                if matrix.rows == 1 && matrix.cols == 1 && matrix.elements.len() == 1 =>
            {
                Ok(matrix.elements.pop().unwrap())
            }
            (Type::Real, _) => Err(ElaborationError::InvalidOperands(
                "a cast to real requires a real scalar or real-valued 1x1 matrix",
            )),
            (Type::Matrix(1, 1), Value::Scalar(value))
                if matches!(concrete_type(self.environment, &value)?, Type::Real) =>
            {
                matrix_expression(1, 1, vec![value])
            }
            (Type::Matrix(_, _), Value::Scalar(_)) => Err(ElaborationError::Shape(
                "a real scalar can only be cast to a 1x1 matrix",
            )),
            (Type::Bool | Type::Nat | Type::Int | Type::Seq(_), _) => Err(
                ElaborationError::Unsupported("only real and 1x1 matrix casts are supported"),
            ),
            (Type::Matrix(_, _), _) => Err(ElaborationError::InvalidOperands(
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
            let left_type = concrete_type(self.environment, previous)?;
            let right_type = concrete_type(self.environment, current)?;
            if !matches!(left_type, Type::Matrix(_, _)) && !matches!(right_type, Type::Matrix(_, _))
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
                    if matches!(concrete_type(self.environment, inner)?, Type::Matrix(_, _)) =>
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
        RawExpr::Variable(found) if found == variable => RawExpr::NatLiteral(value),
        RawExpr::Hole => RawExpr::Hole,
        RawExpr::ImplicitDimension(dimension) => RawExpr::ImplicitDimension(*dimension),
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
    Expr::with_metadata(expression.meta.clone(), raw)
}

fn substitute_type(
    ty: &TypeExpr<TypedMetadata>,
    variable: &Variable,
    value: u64,
) -> TypeExpr<TypedMetadata> {
    match ty {
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
    side_conditions: &[SideCondition<TypedMetadata, Type>],
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
        self.error = match &node.raw {
            RawExpr::Hole => Some(ElaborationError::Unsupported(
                "holes are not supported by to_z3",
            )),
            RawExpr::ImplicitDimension(_)
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
            RawExpr::Monop(op, _) if !matches!(op, Monop::Neg) => Some(
                ElaborationError::Unsupported("unary operator remains after concrete elaboration"),
            ),
            RawExpr::Binop(op, _, _) if !matches!(op, Binop::Div) => Some(
                ElaborationError::Unsupported("binary operator remains after concrete elaboration"),
            ),
            RawExpr::Finop(op, _)
                if !matches!(op, Finop::Plus | Finop::Times | Finop::And | Finop::Or) =>
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
        Environment, Expr, Finop, Matrix, NaturalParameter, RawExpr, Type, TypeExpr,
        enumerable_envspec::infer_symbolic_type_environment,
        from_tex,
        preprocessing::prepare_expression,
        type_resolver::TypedMetadata,
        visit::{self, Visit},
        visit_mut::VisitContext,
    };

    const POSITIVE: VisitContext = VisitContext {
        logical_polarity: true,
    };

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
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
                "diag operand must be a sequence variable"
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
    fn side_condition_types_and_definitions_are_concretized() {
        let (prepared, _) = prepare(r"A^{\frac{1}{2}}", &[r"A \in \mathbb{R}^{2 \times 2}"]);
        let elaborated = elaborate(&Environment::default(), &prepared).unwrap();
        let [condition] = elaborated.side_conditions.as_slice() else {
            panic!("expected one square-root side condition")
        };
        assert_eq!(condition.introduced_type, Type::Matrix(2, 2));
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
