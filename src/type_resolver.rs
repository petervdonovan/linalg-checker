use std::{collections::HashMap, error::Error, fmt};

use crate::{
    Binop, Environment, Expr, Finop, LogicChain, Matrix, Monop, RawExpr, SeqOp, Triop, Type,
    TypeExpr, Variable,
    visit_mut::{VisitContext, VisitMut},
};

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
        self.0 = Some(ty);
    }
}

pub trait TypeLookup {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeRuleOperand {
    value_type: Option<TypeExpr<()>>,
    expression: Expr<()>,
}

impl TypeRuleOperand {
    fn value(&self) -> Result<TypeExpr<()>, TypeError> {
        self.value_type
            .clone()
            .ok_or(TypeError::Invalid("expected a value operand"))
    }

    fn type_expression(&self) -> Result<TypeExpr<()>, TypeError> {
        match &self.expression.raw {
            RawExpr::Type(ty) => Ok(ty.clone()),
            _ => Err(TypeError::Invalid("expected a type-expression operand")),
        }
    }

    pub fn expression(&self) -> &Expr<()> {
        &self.expression
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

    pub fn standard() -> Self {
        let mut rules = Self::core();
        crate::operator_visitors::register_type_rules(&mut rules);
        rules
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

    fn infer_monop(
        &self,
        op: Monop,
        operands: &[TypeRuleOperand],
    ) -> Result<TypeExpr<()>, TypeError> {
        self.monops
            .get(&op)
            .ok_or(TypeError::Unsupported("unregistered unary operator"))?(operands)
    }
    fn infer_binop(
        &self,
        op: Binop,
        operands: &[TypeRuleOperand],
    ) -> Result<TypeExpr<()>, TypeError> {
        self.binops
            .get(&op)
            .ok_or(TypeError::Unsupported("unregistered binary operator"))?(operands)
    }
    fn infer_triop(
        &self,
        op: Triop,
        operands: &[TypeRuleOperand],
    ) -> Result<TypeExpr<()>, TypeError> {
        self.triops
            .get(&op)
            .ok_or(TypeError::Unsupported("unregistered ternary operator"))?(operands)
    }
    fn infer_finop(
        &self,
        op: Finop,
        operands: &[TypeRuleOperand],
    ) -> Result<TypeExpr<()>, TypeError> {
        self.finops
            .get(&op)
            .ok_or(TypeError::Unsupported("unregistered finite operator"))?(operands)
    }
    fn infer_seqop(
        &self,
        op: SeqOp,
        operands: &[TypeRuleOperand],
    ) -> Result<TypeExpr<()>, TypeError> {
        self.seqops
            .get(&op)
            .ok_or(TypeError::Unsupported("unregistered sequence operator"))?(operands)
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

impl TypeLookup for Environment {
    fn type_of(&self, variable: &Variable) -> Option<TypeExpr<()>> {
        self.types
            .get(variable)
            .cloned()
            .map(type_expr)
            .or_else(|| {
                self.equalities
                    .contains_key(&Expr::new(RawExpr::Variable(variable.clone())))
                    .then_some(TypeExpr::Nat)
            })
    }
}

pub struct TypeResolver<'a, Lookup> {
    types: &'a Lookup,
    rules: &'a OperatorTypeRules,
    lexical_types: HashMap<Variable, TypeExpr<()>>,
    error: Option<TypeError>,
}

impl<'a, Lookup: TypeLookup> TypeResolver<'a, Lookup> {
    pub fn new(types: &'a Lookup, rules: &'a OperatorTypeRules) -> Self {
        Self {
            types,
            rules,
            lexical_types: HashMap::new(),
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
                    panic!(
                        "variable {} has no symbolically inferred type",
                        variable.z3_name()
                    )
                }),
            RawExpr::NatLiteral(_) => TypeExpr::Nat,
            RawExpr::Matrix(matrix) => infer_matrix_type(matrix)?,
            RawExpr::Monop(op, inner) => self.rules.infer_monop(*op, &[operand(inner)])?,
            RawExpr::Binop(op, left, right) => self
                .rules
                .infer_binop(*op, &[operand(left), operand(right)])?,
            RawExpr::Triop(op, first, second, third) => self
                .rules
                .infer_triop(*op, &[operand(first), operand(second), operand(third)])?,
            RawExpr::Finop(op, expressions) => self
                .rules
                .infer_finop(*op, &expressions.iter().map(operand).collect::<Vec<_>>())?,
            RawExpr::CmpChain(_) | RawExpr::LogicChain(_) => TypeExpr::Bool,
            RawExpr::Seqop(op, _, body) => self.rules.infer_seqop(*op, &[operand(body)])?,
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
                | RawExpr::IdentityMatrix { .. }
                | RawExpr::ZeroMatrix { .. }
                | RawExpr::Variable(_)
                | RawExpr::NatLiteral(_) => {}
                RawExpr::StandardBasis { index, .. } => self.visit_expr_mut(context, index),
                RawExpr::Type(_) => {}
                RawExpr::Matrix(matrix) => {
                    for element in &mut matrix.elements {
                        self.visit_expr_mut(context, element);
                    }
                }
                RawExpr::Monop(_, inner) => self.visit_expr_mut(context, inner),
                RawExpr::Binop(Binop::ElementOf, left, right) => {
                    if !matches!(left.raw, RawExpr::Variable(_)) {
                        self.visit_expr_mut(context, left);
                    }
                    self.visit_expr_mut(context, right);
                }
                RawExpr::Binop(Binop::Cast, _, value) => self.visit_expr_mut(context, value),
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
}

fn node_type<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> Result<TypeExpr<()>, TypeError> {
    expression.meta.get_type()
}

fn operand<Metadata: MaybeTyped>(expression: &Expr<Metadata>) -> TypeRuleOperand {
    let value_type = match expression.raw {
        RawExpr::Type(_) | RawExpr::Hole => None,
        _ => node_type(expression).ok(),
    };
    TypeRuleOperand {
        value_type,
        expression: expression.with_default_metadata(),
    }
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

pub(crate) fn real_operator_type_rule(
    operands: &[TypeRuleOperand],
) -> Result<TypeExpr<()>, TypeError> {
    real_result_rule(operands)
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
    Expr::new(RawExpr::Variable(Variable::new(value.z3_name())))
}

fn infer_matrix_type<Metadata: MaybeTyped>(
    matrix: &Matrix<Expr<Metadata>>,
) -> Result<TypeExpr<()>, TypeError> {
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
        return Ok(TypeExpr::Matrix(natural(0), natural(0)));
    }

    let dimensions = matrix
        .elements
        .iter()
        .map(|element| block_dimensions(node_type(element)?))
        .collect::<Result<Vec<_>, _>>()?;
    let row_heights = (0..matrix.rows)
        .map(|row| dimensions[row * matrix.cols].0.clone())
        .collect();
    let column_widths = (0..matrix.cols)
        .map(|column| dimensions[column].1.clone())
        .collect();
    Ok(TypeExpr::Matrix(
        sum_dimensions(row_heights),
        sum_dimensions(column_widths),
    ))
}

fn block_dimensions(ty: TypeExpr<()>) -> Result<(Expr<()>, Expr<()>), TypeError> {
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

fn scalar_lub(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
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

fn add_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
    match (left, right) {
        (matrix @ TypeExpr::Matrix(_, _), TypeExpr::Matrix(_, _)) => Ok(matrix),
        (TypeExpr::Matrix(_, _), _) | (_, TypeExpr::Matrix(_, _)) => Err(TypeError::Invalid(
            "matrix and scalar addition is unsupported",
        )),
        (left, right) => scalar_lub(left, right),
    }
}

fn multiply_type(left: TypeExpr<()>, right: TypeExpr<()>) -> Result<TypeExpr<()>, TypeError> {
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
        TypeResolver::new(&types, &OperatorTypeRules::standard())
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
        TypeResolver::new(&types, &OperatorTypeRules::standard())
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
    fn missing_and_duplicate_operator_rules_are_explicit() {
        let types = SymbolicTypeEnvironment {
            types: HashMap::from([(Variable::new("x"), TypeExpr::Real)]),
        };
        let parsed: Expr<()> = from_tex::expr(&parse("x^2").unwrap()).unwrap();
        let mut expression: Expr<TypedMetadata> = parsed.with_default_metadata();
        assert!(matches!(
            TypeResolver::new(&types, &OperatorTypeRules::new()).resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true
                },
            ),
            Err(super::TypeError::Unsupported(_))
        ));

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
    fn core_rules_reject_surface_norms() {
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
        assert!(matches!(
            TypeResolver::new(&types, &OperatorTypeRules::core()).resolve(
                &mut expression,
                VisitContext {
                    logical_polarity: true
                },
            ),
            Err(super::TypeError::Unsupported(_))
        ));
    }
}
