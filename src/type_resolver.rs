use std::{collections::HashMap, error::Error, fmt};

use crate::{
    Binop, Expr, Finop, LogicChain, Matrix, Monop, RawExpr, SeqOp, Triop, TypeExpr, Variable,
    visit_mut::{VisitContext, VisitMut},
};

#[cfg(test)]
use crate::Type;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    MissingType(Variable),
    Invalid(&'static str),
    Unsupported(&'static str),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingType(variable) => write!(f, "missing type for {}", variable.z3_name()),
            Self::Invalid(message) | Self::Unsupported(message) => f.write_str(message),
        }
    }
}

impl Error for TypeError {}

pub trait MaybeTyped {
    fn get_type(&self) -> Result<TypeExpr<()>, TypeError>;
    fn put_type(&mut self, ty: TypeExpr<()>);
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypedMetadata(Option<TypeExpr<()>>);

impl MaybeTyped for TypedMetadata {
    fn get_type(&self) -> Result<TypeExpr<()>, TypeError> {
        self.0
            .clone()
            .ok_or(TypeError::Unsupported("expression has no value type"))
    }

    fn put_type(&mut self, ty: TypeExpr<()>) {
        if let Some(previous) = &self.0 {
            assert_eq!(
                previous, &ty,
                "type resolution changed an existing annotation"
            );
        } else {
            self.0 = Some(ty);
        }
    }
}

impl TypedMetadata {
    pub(crate) fn resolved(ty: TypeExpr<()>) -> Self {
        Self(Some(ty))
    }
}

pub trait TypeLookup {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeRuleOperand {
    Value(TypeExpr<()>),
    TypeExpression(TypeExpr<()>),
    NoValue,
}

impl TypeRuleOperand {
    fn value(&self) -> Result<TypeExpr<()>, TypeError> {
        match self {
            Self::Value(ty) => Ok(ty.clone()),
            Self::TypeExpression(_) | Self::NoValue => {
                Err(TypeError::Invalid("expected a value operand"))
            }
        }
    }

    fn type_expression(&self) -> Result<TypeExpr<()>, TypeError> {
        match self {
            Self::TypeExpression(ty) => Ok(ty.clone()),
            Self::Value(_) | Self::NoValue => {
                Err(TypeError::Invalid("expected a type-expression operand"))
            }
        }
    }
}

pub type TypeRule = fn(&[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError>;

#[derive(Clone, Default)]
pub struct OperatorTypeRules {
    monops: HashMap<Monop, TypeRule>,
    binops: HashMap<Binop, TypeRule>,
    triops: HashMap<Triop, TypeRule>,
    finops: HashMap<Finop, TypeRule>,
    seqops: HashMap<SeqOp, TypeRule>,
}

impl OperatorTypeRules {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register_monop(&mut self, op: Monop, rule: TypeRule) {
        assert!(
            self.monops.insert(op, rule).is_none(),
            "duplicate unary type rule"
        );
    }
    pub fn register_binop(&mut self, op: Binop, rule: TypeRule) {
        assert!(
            self.binops.insert(op, rule).is_none(),
            "duplicate binary type rule"
        );
    }
    pub fn register_triop(&mut self, op: Triop, rule: TypeRule) {
        assert!(
            self.triops.insert(op, rule).is_none(),
            "duplicate ternary type rule"
        );
    }
    pub fn register_finop(&mut self, op: Finop, rule: TypeRule) {
        assert!(
            self.finops.insert(op, rule).is_none(),
            "duplicate finite type rule"
        );
    }
    pub fn register_seqop(&mut self, op: SeqOp, rule: TypeRule) {
        assert!(
            self.seqops.insert(op, rule).is_none(),
            "duplicate sequence type rule"
        );
    }

    pub fn core() -> Self {
        let mut rules = Self::new();
        rules.register_monop(Monop::Neg, numeric_identity_rule);
        rules.register_monop(Monop::Transpose, transpose_rule);
        for op in [
            Monop::Trace,
            Monop::Det,
            Monop::Norm1,
            Monop::NormInfty,
            Monop::NormFrob,
        ] {
            rules.register_monop(op, real_result_rule);
        }
        rules.register_monop(Monop::Inverse, matrix_identity_rule);
        rules.register_binop(Binop::Div, division_rule);
        rules.register_binop(Binop::Power, first_value_rule);
        rules.register_binop(Binop::InnerProd, real_result_rule);
        rules.register_binop(Binop::Cast, cast_rule);
        rules.register_binop(Binop::ElementOf, bool_result_rule);
        rules.register_binop(Binop::SingleSubscript, subscript_rule);
        rules.register_triop(Triop::DoubleSubscript, real_result_rule);
        rules.register_finop(Finop::Plus, addition_rule);
        rules.register_finop(Finop::Times, multiplication_rule);
        rules.register_finop(Finop::And, bool_result_rule);
        rules.register_finop(Finop::Or, bool_result_rule);
        rules.register_finop(Finop::Max, scalar_fold_rule);
        rules.register_finop(Finop::Min, scalar_fold_rule);
        rules.register_seqop(SeqOp::Sum, first_value_rule);
        rules.register_seqop(SeqOp::Prod, first_value_rule);
        rules
    }

    pub(crate) fn supports_monop(&self, op: Monop) -> bool {
        self.monops.contains_key(&op)
    }

    pub(crate) fn supports_binop(&self, op: Binop) -> bool {
        self.binops.contains_key(&op)
    }

    pub(crate) fn supports_triop(&self, op: Triop) -> bool {
        self.triops.contains_key(&op)
    }

    pub(crate) fn supports_finop(&self, op: Finop) -> bool {
        self.finops.contains_key(&op)
    }

    pub(crate) fn supports_seqop(&self, op: SeqOp) -> bool {
        self.seqops.contains_key(&op)
    }

    fn infer_monop(
        &self,
        op: Monop,
        operands: &[TypeRuleOperand],
    ) -> Option<Result<TypeExpr<()>, TypeError>> {
        self.monops.get(&op).map(|rule| rule(operands))
    }
    fn infer_binop(
        &self,
        op: Binop,
        operands: &[TypeRuleOperand],
    ) -> Option<Result<TypeExpr<()>, TypeError>> {
        self.binops.get(&op).map(|rule| rule(operands))
    }
    fn infer_triop(
        &self,
        op: Triop,
        operands: &[TypeRuleOperand],
    ) -> Option<Result<TypeExpr<()>, TypeError>> {
        self.triops.get(&op).map(|rule| rule(operands))
    }
    fn infer_finop(
        &self,
        op: Finop,
        operands: &[TypeRuleOperand],
    ) -> Option<Result<TypeExpr<()>, TypeError>> {
        self.finops.get(&op).map(|rule| rule(operands))
    }
    fn infer_seqop(
        &self,
        op: SeqOp,
        operands: &[TypeRuleOperand],
    ) -> Option<Result<TypeExpr<()>, TypeError>> {
        self.seqops.get(&op).map(|rule| rule(operands))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolicTypeEnvironment {
    pub types: HashMap<Variable, TypeExpr<()>>,
}

impl TypeLookup for SymbolicTypeEnvironment {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>> {
        self.types.get(variable).cloned()
    }
}

pub struct TypeResolver<'a, Lookup> {
    types: &'a Lookup,
    rules: &'a OperatorTypeRules,
    lexical_types: HashMap<Variable, TypeExpr<()>>,
    in_dimension_expression: bool,
    error: Option<TypeError>,
}

impl<'a, Lookup: TypeLookup> TypeResolver<'a, Lookup> {
    pub fn new(types: &'a Lookup, rules: &'a OperatorTypeRules) -> Self {
        Self {
            types,
            rules,
            lexical_types: HashMap::new(),
            in_dimension_expression: false,
            error: None,
        }
    }

    pub fn resolve<Metadata: MaybeTyped>(
        mut self,
        expression: &mut Expr<Metadata>,
        context: VisitContext,
    ) -> Result<(), TypeError> {
        self.visit_expr_mut(context, expression);
        self.error.map_or(Ok(()), Err)
    }

    fn infer<Metadata: MaybeTyped>(
        &self,
        expression: &Expr<Metadata>,
    ) -> Result<Option<TypeExpr<()>>, TypeError> {
        let ty = match &expression.raw {
            RawExpr::Hole | RawExpr::Type(_) => return Ok(None),
            RawExpr::ImplicitDimension(_) => TypeExpr::Nat,
            RawExpr::IdentityMatrix { dimension } => {
                let dimension = implicit_dimension(*dimension);
                TypeExpr::Matrix(dimension.clone(), dimension)
            }
            RawExpr::StandardBasis { dimension, .. } => {
                TypeExpr::Matrix(implicit_dimension(*dimension), natural(1))
            }
            RawExpr::ZeroMatrix { rows, cols } => {
                TypeExpr::Matrix(implicit_dimension(*rows), implicit_dimension(*cols))
            }
            RawExpr::Variable(variable) => self
                .lexical_types
                .get(variable)
                .cloned()
                .or_else(|| self.types.type_of(variable))
                .unwrap_or_else(|| {
                    if self.in_dimension_expression {
                        return TypeExpr::Nat;
                    }
                    panic!(
                        "variable {} has no symbolically inferred type",
                        variable.z3_name()
                    )
                }),
            RawExpr::NatLiteral(_) => TypeExpr::Nat,
            RawExpr::Matrix(matrix) => return infer_matrix_type(matrix),
            RawExpr::Monop(op, inner) => {
                return infer_operator([inner], |operands| self.rules.infer_monop(*op, operands));
            }
            RawExpr::Binop(Binop::ElementOf, _, _) => TypeExpr::Bool,
            RawExpr::Binop(Binop::Cast, target, value) => {
                let Some(value) = operand(value) else {
                    return Ok(None);
                };
                let target = match &target.raw {
                    RawExpr::Type(ty) => {
                        TypeRuleOperand::TypeExpression(ty.with_default_metadata())
                    }
                    _ => TypeRuleOperand::NoValue,
                };
                return self
                    .rules
                    .infer_binop(Binop::Cast, &[target, value])
                    .transpose();
            }
            RawExpr::Binop(op, left, right) => {
                return infer_operator([left, right], |operands| {
                    self.rules.infer_binop(*op, operands)
                });
            }
            RawExpr::Triop(op, first, second, third) => {
                return infer_operator([first, second, third], |operands| {
                    self.rules.infer_triop(*op, operands)
                });
            }
            RawExpr::Finop(op, expressions) => {
                return infer_operator(expressions.iter(), |operands| {
                    self.rules.infer_finop(*op, operands)
                });
            }
            RawExpr::CmpChain(_) | RawExpr::LogicChain(_) => TypeExpr::Bool,
            RawExpr::Seqop(op, _, body) => {
                return infer_operator([body], |operands| self.rules.infer_seqop(*op, operands));
            }
        };
        Ok(Some(ty))
    }
}

impl<Metadata: MaybeTyped, Lookup: TypeLookup> VisitMut<Metadata> for TypeResolver<'_, Lookup> {
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        let _logical_polarity = context.logical_polarity;
        if self.error.is_some() {
            return;
        }
        {
            let raw = &mut node
                .get_mut()
                .expect("type resolution requires unique expressions")
                .raw;
            match raw {
                RawExpr::Hole
                | RawExpr::ImplicitDimension(_)
                | RawExpr::IdentityMatrix { .. }
                | RawExpr::ZeroMatrix { .. }
                | RawExpr::Variable(_)
                | RawExpr::NatLiteral(_) => {}
                RawExpr::StandardBasis { index, .. } => self.visit_expr_mut(context, index),
                RawExpr::Type(ty) => self.visit_type_expr_mut(context, ty),
                RawExpr::Matrix(matrix) => {
                    for element in &mut matrix.elements {
                        self.visit_expr_mut(context, element);
                    }
                }
                RawExpr::Monop(_, inner) => self.visit_expr_mut(context, inner),
                RawExpr::Binop(Binop::ElementOf, left, right) => {
                    self.visit_expr_mut(context, left);
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Binop(Binop::Cast, target, value) => {
                    if matches!(target.raw, RawExpr::Type(_)) {
                        self.visit_expr_mut(context, target);
                    }
                    self.visit_expr_mut(context, value);
                }
                RawExpr::Binop(_, left, right) => {
                    self.visit_expr_mut(context, left);
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Triop(_, a, b, c) => {
                    self.visit_expr_mut(context, a);
                    self.visit_expr_mut(context, b);
                    self.visit_expr_mut(context, c);
                }
                RawExpr::Finop(_, expressions) => {
                    for expression in expressions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::CmpChain(chain) => {
                    self.visit_expr_mut(context, &mut chain.start);
                    for (_, expression) in &mut chain.assertions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::LogicChain(LogicChain { start, assertions }) => {
                    self.visit_expr_mut(context, start);
                    for (_, expression) in assertions {
                        self.visit_expr_mut(context, expression);
                    }
                }
                RawExpr::Seqop(_, range, body) => {
                    self.visit_expr_mut(context, &mut range.from);
                    self.visit_expr_mut(context, &mut range.to);
                    if self.lexical_types.contains_key(&range.index_variable)
                        || self.types.type_of(&range.index_variable).is_some()
                    {
                        self.error = Some(TypeError::Invalid(
                            "sequence index collides with a global variable or enclosing binder",
                        ));
                        return;
                    }
                    let previous = self
                        .lexical_types
                        .insert(range.index_variable.clone(), TypeExpr::Nat);
                    self.visit_expr_mut(context, body);
                    assert!(previous.is_none());
                    self.lexical_types.remove(&range.index_variable);
                }
            }
        }
        if self.error.is_some() {
            return;
        }
        match self.infer(node) {
            Ok(Some(ty)) => node.get_mut().unwrap().meta.put_type(ty),
            Ok(None) => {}
            Err(error) => self.error = Some(error),
        }
    }

    fn visit_type_expr_mut(&mut self, context: VisitContext, node: &mut TypeExpr<Metadata>) {
        match node {
            TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
            TypeExpr::Matrix(rows, cols) => {
                let previous = self.in_dimension_expression;
                self.in_dimension_expression = true;
                self.visit_expr_mut(context, rows);
                self.visit_expr_mut(context, cols);
                self.in_dimension_expression = previous;
            }
            TypeExpr::Seq(element, size) => {
                self.visit_expr_mut(context, element);
                let previous = self.in_dimension_expression;
                self.in_dimension_expression = true;
                self.visit_expr_mut(context, size);
                self.in_dimension_expression = previous;
            }
        }
    }
}

fn node_type<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> Result<TypeExpr<()>, TypeError> {
    expression.meta.get_type()
}

fn operand<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> Option<TypeRuleOperand> {
    match &expression.raw {
        RawExpr::Type(ty) => Some(TypeRuleOperand::TypeExpression(ty.with_default_metadata())),
        RawExpr::Hole => Some(TypeRuleOperand::NoValue),
        _ => node_type(expression).map(TypeRuleOperand::Value).ok(),
    }
}

fn infer_operator<'a, Metadata: MaybeTyped + 'a>(
    expressions: impl IntoIterator<Item = &'a Expr<Metadata>>,
    infer: impl FnOnce(&[TypeRuleOperand]) -> Option<Result<TypeExpr<()>, TypeError>>,
) -> Result<Option<TypeExpr<()>>, TypeError> {
    let Some(operands) = expressions
        .into_iter()
        .map(operand)
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };
    infer(&operands).transpose()
}

fn exactly(operands: &[TypeRuleOperand], count: usize) -> Result<&[TypeRuleOperand], TypeError> {
    (operands.len() == count)
        .then_some(operands)
        .ok_or(TypeError::Invalid(
            "operator has the wrong number of operands",
        ))
}

fn first_value_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    if !(1..=2).contains(&operands.len()) {
        return Err(TypeError::Invalid(
            "operator has the wrong number of operands",
        ));
    }
    operands
        .first()
        .ok_or(TypeError::Invalid("operator is missing an operand"))?
        .value()
}

fn numeric_identity_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    require_numeric(exactly(operands, 1)?[0].value()?)
}

fn matrix_identity_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    match exactly(operands, 1)?[0].value()? {
        matrix @ TypeExpr::Matrix(_, _) => Ok(matrix),
        _ => Err(TypeError::Invalid("operation requires a matrix")),
    }
}

fn transpose_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    match exactly(operands, 1)?[0].value()? {
        TypeExpr::Matrix(rows, cols) => Ok(TypeExpr::Matrix(cols, rows)),
        _ => Err(TypeError::Invalid("transpose requires a matrix")),
    }
}

fn real_result_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    if operands.is_empty() {
        return Err(TypeError::Invalid("operator is missing an operand"));
    }
    for operand in operands {
        operand.value()?;
    }
    Ok(TypeExpr::Real)
}

fn bool_result_rule(_operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    Ok(TypeExpr::Bool)
}

fn cast_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    let operands = exactly(operands, 2)?;
    operands[1].value()?;
    match operands[0].type_expression() {
        Ok(ty) => Ok(ty),
        Err(_) => operands[1].value(),
    }
}

fn subscript_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    let operands = exactly(operands, 2)?;
    operands[1].value()?;
    let TypeExpr::Seq(element, _) = operands[0].value()? else {
        return Err(TypeError::Invalid(
            "subscripted expression is not a sequence",
        ));
    };
    let RawExpr::Type(element) = &element.raw else {
        return Err(TypeError::Invalid(
            "sequence element must be a type expression",
        ));
    };
    Ok(element.clone())
}

fn division_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    let operands = exactly(operands, 2)?;
    division_type(operands[0].value()?, operands[1].value()?)
}

fn fold_operand_types(
    operands: &[TypeRuleOperand],
    operation: BinaryTypeOperation,
) -> Result<TypeExpr<()>, TypeError> {
    let mut operands = operands.iter();
    let first = operands
        .next()
        .ok_or(TypeError::Invalid("finite operation is empty"))?
        .value()?;
    operands.try_fold(first, |left, right| operation(left, right.value()?))
}

fn addition_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    if operands.is_empty() {
        return Ok(TypeExpr::Real);
    }
    fold_operand_types(operands, add_type)
}
fn multiplication_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    if operands.is_empty() {
        return Ok(TypeExpr::Real);
    }
    fold_operand_types(operands, multiply_type)
}
fn scalar_fold_rule(operands: &[TypeRuleOperand]) -> Result<TypeExpr<()>, TypeError> {
    fold_operand_types(operands, scalar_lub)
}

#[cfg(test)]
pub(crate) fn type_expr(ty: Type) -> TypeExpr<()> {
    match ty {
        Type::Bool => TypeExpr::Bool,
        Type::Nat => TypeExpr::Nat,
        Type::Int => TypeExpr::Int,
        Type::Real => TypeExpr::Real,
        Type::Matrix(rows, cols) => TypeExpr::Matrix(natural(rows), natural(cols)),
        Type::Seq(sequence) => TypeExpr::Seq(
            Expr::new(RawExpr::Type(type_expr(sequence.t))),
            natural(sequence.n),
        ),
    }
}

fn natural(value: u64) -> Expr<()> {
    Expr::new(RawExpr::NatLiteral(value))
}
fn implicit_dimension(value: crate::ImplicitDimension) -> Expr<()> {
    Expr::new(RawExpr::ImplicitDimension(value))
}

fn infer_matrix_type<Metadata: MaybeTyped>(
    matrix: &Matrix<Expr<Metadata>>,
) -> Result<Option<TypeExpr<()>>, TypeError> {
    let expected_elements = matrix
        .rows
        .checked_mul(matrix.cols)
        .ok_or(TypeError::Invalid("matrix dimensions overflow usize"))?;
    if matrix.elements.len() != expected_elements {
        return Err(TypeError::Invalid(
            "matrix element count does not match its dimensions",
        ));
    }
    if (matrix.rows == 0) != (matrix.cols == 0) {
        return Err(TypeError::Invalid(
            "matrix dimensions must both be zero or both be nonzero",
        ));
    }
    if matrix.rows == 0 {
        return Ok(Some(TypeExpr::Matrix(natural(0), natural(0))));
    }

    let mut dimensions = Vec::with_capacity(matrix.elements.len());
    for element in &matrix.elements {
        let Ok(ty) = node_type(element) else {
            return Ok(None);
        };
        dimensions.push(block_dimensions(ty)?);
    }
    let row_heights = (0..matrix.rows)
        .map(|row| dimensions[row * matrix.cols].0.clone())
        .collect();
    let column_widths = (0..matrix.cols)
        .map(|column| dimensions[column].1.clone())
        .collect();
    Ok(Some(TypeExpr::Matrix(
        sum_dimensions(row_heights),
        sum_dimensions(column_widths),
    )))
}

pub(crate) fn block_dimensions(ty: TypeExpr<()>) -> Result<(Expr<()>, Expr<()>), TypeError> {
    match ty {
        TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => Ok((natural(1), natural(1))),
        TypeExpr::Matrix(rows, cols) if is_zero_dimension(&rows) && is_zero_dimension(&cols) => {
            Err(TypeError::Invalid(
                "empty matrices cannot be used as blocks",
            ))
        }
        TypeExpr::Matrix(rows, cols) => Ok((rows, cols)),
        TypeExpr::Bool | TypeExpr::Seq(_, _) => Err(TypeError::Invalid(
            "block matrix cells must be numeric scalars or matrices",
        )),
    }
}

fn is_zero_dimension(expression: &Expr<()>) -> bool {
    matches!(expression.raw, RawExpr::NatLiteral(0))
}

fn sum_dimensions(mut dimensions: Vec<Expr<()>>) -> Expr<()> {
    match dimensions.len() {
        0 => natural(0),
        1 => dimensions.pop().unwrap(),
        _ => Expr::new(RawExpr::Finop(Finop::Plus, dimensions)),
    }
}

type BinaryTypeOperation = fn(TypeExpr<()>, TypeExpr<()>) -> Result<TypeExpr<()>, TypeError>;

fn require_numeric(ty: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match ty {
        TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real | TypeExpr::Matrix(_, _) => Ok(ty),
        _ => Err(TypeError::Invalid("operation requires numeric operands")),
    }
}

pub(crate) fn require_numeric_scalar(ty: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match ty {
        TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => Ok(ty),
        _ => Err(TypeError::Invalid(
            "operation requires numeric scalar operands",
        )),
    }
}

pub(crate) fn scalar_lub(
    left: TypeExpr<()>,
    right: TypeExpr<()>,
) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (TypeExpr::Nat, TypeExpr::Nat) => Ok(TypeExpr::Nat),
        (TypeExpr::Nat | TypeExpr::Int, TypeExpr::Nat | TypeExpr::Int) => Ok(TypeExpr::Int),
        (
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
            TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real,
        ) => Ok(TypeExpr::Real),
        _ => Err(TypeError::Invalid(
            "operation requires numeric scalar operands",
        )),
    }
}

pub(crate) fn add_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (matrix @ TypeExpr::Matrix(_, _), TypeExpr::Matrix(_, _)) => Ok(matrix),
        (TypeExpr::Matrix(_, _), _) | (_, TypeExpr::Matrix(_, _)) => Err(TypeError::Invalid(
            "matrix and scalar addition is unsupported",
        )),
        (left, right) => scalar_lub(left, right),
    }
}

pub(crate) fn multiply_type(
    left: TypeExpr<()>,
    right: TypeExpr<()>,
) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (TypeExpr::Matrix(rows, _), TypeExpr::Matrix(_, cols)) => Ok(TypeExpr::Matrix(rows, cols)),
        (matrix @ TypeExpr::Matrix(_, _), scalar) | (scalar, matrix @ TypeExpr::Matrix(_, _)) => {
            require_numeric(scalar)?;
            Ok(matrix)
        }
        (left, right) => scalar_lub(left, right),
    }
}

fn division_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    let scalar = |ty| match ty {
        TypeExpr::Matrix(_, _) => Ok(TypeExpr::Real),
        other => Ok(other),
    };
    scalar_lub(scalar(left)?, scalar(right)?)
}

#[cfg(test)]
mod tests {
    use super::{
        MaybeTyped, OperatorTypeRules, SymbolicTypeEnvironment, TypeResolver, TypedMetadata,
    };
    use crate::{
        Binop, Expr, Finop, RawExpr, TypeExpr, Variable, from_tex, visit_mut::VisitContext,
    };
    use ratex_parser::parse;
    use std::collections::HashMap;

    #[test]
    fn resolves_symbolic_matrix_dimensions_without_concretizing_them() {
        let n = Expr::new(RawExpr::Variable(Variable::new("n")));
        let p = Expr::new(RawExpr::Variable(Variable::new("p")));
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([
                (Variable::new("A"), TypeExpr::Matrix(n.clone(), p.clone())),
                (Variable::new("B"), TypeExpr::Matrix(p, n.clone())),
            ]),
        };
        let parsed: Expr<()> = from_tex::expr(&parse("A B").unwrap()).unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        TypeResolver::new(&types, &OperatorTypeRules::core())
            .resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true,
                },
            )
            .unwrap();
        assert_eq!(
            expression.meta.get_type().unwrap(),
            TypeExpr::Matrix(n.clone(), n)
        );
    }

    #[test]
    fn resolves_symbolic_block_matrix_dimensions() {
        let m = Expr::new(RawExpr::Variable(Variable::new("m")));
        let n = Expr::new(RawExpr::Variable(Variable::new("n")));
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([
                (Variable::new("A"), TypeExpr::Matrix(m.clone(), n.clone())),
                (
                    Variable::new("b"),
                    TypeExpr::Matrix(m.clone(), Expr::new(RawExpr::NatLiteral(1))),
                ),
                (
                    Variable::new("c"),
                    TypeExpr::Matrix(n.clone(), Expr::new(RawExpr::NatLiteral(1))),
                ),
                (Variable::new("d"), TypeExpr::Real),
            ]),
        };
        let parsed: Expr<()> =
            from_tex::expr(&parse(r"\begin{bmatrix}A & b \\ c^\top & d\end{bmatrix}").unwrap())
                .unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        TypeResolver::new(&types, &OperatorTypeRules::core())
            .resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true,
                },
            )
            .unwrap();

        assert_eq!(
            expression.meta.get_type().unwrap(),
            TypeExpr::Matrix(
                Expr::new(RawExpr::Finop(
                    Finop::Plus,
                    vec![m, Expr::new(RawExpr::NatLiteral(1))],
                )),
                Expr::new(RawExpr::Finop(
                    Finop::Plus,
                    vec![n, Expr::new(RawExpr::NatLiteral(1))],
                )),
            )
        );
    }

    #[test]
    fn missing_rules_defer_typing_and_duplicate_rules_are_explicit() {
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(Variable::new("x"), TypeExpr::Real)]),
        };
        let parsed: Expr<()> = from_tex::expr(&parse("x^2").unwrap()).unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        TypeResolver::new(&types, &OperatorTypeRules::new())
            .resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true,
                },
            )
            .unwrap();
        assert!(expression.meta.get_type().is_err());

        let mut rules = OperatorTypeRules::new();
        rules.register_binop(Binop::Power, super::first_value_rule);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                rules.register_binop(Binop::Power, super::first_value_rule);
            }))
            .is_err()
        );
    }

    #[test]
    fn core_rules_leave_surface_norms_untyped_but_type_their_operands() {
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(
                Variable::new("v"),
                TypeExpr::Matrix(
                    Expr::new(RawExpr::NatLiteral(2)),
                    Expr::new(RawExpr::NatLiteral(1)),
                ),
            )]),
        };
        let parsed: Expr<()> =
            from_tex::expr(&parse(r"\left\lVert v \right\rVert_2").unwrap()).unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        TypeResolver::new(&types, &OperatorTypeRules::core())
            .resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true,
                },
            )
            .unwrap();
        assert!(expression.meta.get_type().is_err());
        let RawExpr::Monop(crate::Monop::Norm2, operand) = &expression.raw else {
            panic!("expected a 2-norm")
        };
        assert!(matches!(
            operand.meta.get_type(),
            Ok(TypeExpr::Matrix(_, _))
        ));
    }

    #[test]
    fn type_resolution_never_changes_an_existing_annotation() {
        let variable = Variable::new("x");
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(variable.clone(), TypeExpr::Real)]),
        };
        let mut expression = Expr::with_metadata(
            TypedMetadata(Some(TypeExpr::Nat)),
            RawExpr::Variable(variable),
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                TypeResolver::new(&types, &OperatorTypeRules::core())
                    .resolve(
                        &mut expression,
                        VisitContext {
                            logical_polarity: true,
                        },
                    )
                    .unwrap();
            }))
            .is_err()
        );
    }
}
