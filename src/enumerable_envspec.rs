use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    error::Error,
    fmt,
};

use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

use crate::{
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Monop, RawExpr, SeqOp, SeqType, Type, TypeExpr,
    Variable,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShapeError {
    Unsat(String),
    Unsupported(String),
    InvalidTyping(String),
    Unknown(String),
}

impl fmt::Display for ShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsat(reason) => write!(f, "shape constraints are unsatisfiable: {reason}"),
            Self::Unsupported(reason) => write!(f, "unsupported shape constraint: {reason}"),
            Self::InvalidTyping(reason) => write!(f, "invalid shape typing: {reason}"),
            Self::Unknown(reason) => write!(f, "Z3 could not decide shape constraints: {reason}"),
        }
    }
}

impl Error for ShapeError {}

#[derive(Clone)]
enum Shape {
    Bool,
    Nat,
    Int,
    Real,
    Matrix(Int, Int),
    Seq(Box<Shape>, Int),
}

pub struct EnvironmentIterator {
    solver: Solver,
    variable_types: BTreeMap<Variable, Shape>,
    dimensions: Vec<Int>,
    known_equalities: HashMap<Expr<()>, u64>,
    projections: Vec<(Expr<()>, Int)>,
    dim_limit: u64,
    max_dimension: u64,
    dimensionless_yielded: bool,
    finished: bool,
}

pub fn extract_environment_iterator<Metadata>(
    assumptions: impl Iterator<Item = Expr<Metadata>>,
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    let assumptions: Vec<_> = assumptions.map(|e| e.without_metadata()).collect();
    let specification = collect_environment_specification(&assumptions)?;
    let mut solver = Solver::new();
    let variable_types = infer_variable_types(&mut solver, specification)?;
    assert_positive_matrix_dimensions(&mut solver, &variable_types);
    let (known_equalities, projections) = {
        let mut projections = BTreeMap::new();
        let mut context = ShapeContext {
            solver: &mut solver,
            variable_types: &variable_types,
            projections: &mut projections,
        };
        for assumption in &assumptions {
            context.constrain_assertion(assumption)?;
        }
        let known = context.known_equalities(&assumptions)?;
        (known, projections.into_iter().collect())
    };
    check_base_constraints(&mut solver)?;

    let dimensions: Vec<Int> = variable_types.values().flat_map(shape_dimensions).collect();
    let finished = !dimensions.is_empty() && max_dimension == 0;
    let mut iterator = EnvironmentIterator {
        solver,
        variable_types,
        dimensions,
        known_equalities,
        projections,
        dim_limit: 1,
        max_dimension,
        dimensionless_yielded: false,
        finished,
    };
    if !iterator.dimensions.is_empty() && !iterator.finished {
        iterator.push_dim_limit();
    }
    Ok(iterator)
}

struct EnvironmentSpecification {
    variables: BTreeSet<Variable>,
    explicit_types: BTreeMap<Variable, Vec<TypeExpr<()>>>,
    dimension_variables: BTreeSet<Variable>,
}

fn collect_environment_specification(
    assumptions: &[Expr<()>],
) -> Result<EnvironmentSpecification, ShapeError> {
    let mut specification = EnvironmentSpecification {
        variables: BTreeSet::new(),
        explicit_types: BTreeMap::new(),
        dimension_variables: BTreeSet::new(),
    };
    for assumption in assumptions {
        collect_variables(assumption, &mut specification.variables);
        collect_range_bound_variables(assumption, &mut specification.dimension_variables);
        let RawExpr::Binop(Binop::ElementOf, left, right) = &assumption.raw else {
            continue;
        };
        let RawExpr::Variable(variable) = &left.raw else {
            return Err(ShapeError::InvalidTyping(
                "type membership must have a variable on the left".to_owned(),
            ));
        };
        let RawExpr::Type(ty) = &right.raw else {
            return Err(ShapeError::InvalidTyping(
                "type membership must have a type on the right".to_owned(),
            ));
        };
        collect_type_dimension_variables(ty, &mut specification.dimension_variables);
        specification
            .explicit_types
            .entry(variable.clone())
            .or_default()
            .push(ty.clone());
    }
    Ok(specification)
}

fn infer_variable_types(
    solver: &mut Solver,
    specification: EnvironmentSpecification,
) -> Result<BTreeMap<Variable, Shape>, ShapeError> {
    let mut variable_types = BTreeMap::new();
    let mut generated_names = BTreeSet::new();
    for variable in specification.variables {
        let explicit = specification
            .explicit_types
            .get(&variable)
            .and_then(|types| types.first());
        let shape = if specification.dimension_variables.contains(&variable) {
            Shape::Nat
        } else if let Some(ty) = explicit {
            shape_from_type_expr(&variable, ty, &mut generated_names)?
        } else {
            guessed_shape(&variable, &mut generated_names)
        };
        if matches!(shape, Shape::Nat) {
            solver.assert(Int::new_const(variable_z3_name(&variable)).ge(0));
        }
        variable_types.insert(variable, shape);
    }
    reject_generated_name_collisions(&variable_types, &generated_names)?;
    Ok(variable_types)
}

fn reject_generated_name_collisions(
    variable_types: &BTreeMap<Variable, Shape>,
    generated_names: &BTreeSet<String>,
) -> Result<(), ShapeError> {
    let user_names: BTreeSet<_> = variable_types.keys().map(variable_z3_name).collect();
    if let Some(collision) = generated_names.intersection(&user_names).next() {
        return Err(ShapeError::InvalidTyping(format!(
            "generated dimension variable collides with user variable {collision}"
        )));
    }
    Ok(())
}

fn assert_positive_matrix_dimensions(
    solver: &mut Solver,
    variable_types: &BTreeMap<Variable, Shape>,
) {
    for shape in variable_types.values() {
        for dimension in shape_dimensions(shape) {
            solver.assert(dimension.gt(0));
        }
    }
}

fn check_base_constraints(solver: &mut Solver) -> Result<(), ShapeError> {
    match solver.check() {
        SatResult::Sat => Ok(()),
        SatResult::Unsat => Err(ShapeError::Unsat(
            "the permanent shape constraints have no model".to_owned(),
        )),
        SatResult::Unknown => Err(ShapeError::Unknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown reason".to_owned()),
        )),
    }
}

impl EnvironmentIterator {
    fn push_dim_limit(&mut self) {
        self.solver.push();
        let limit = Int::from_u64(self.dim_limit);
        for dimension in &self.dimensions {
            self.solver.assert(dimension.le(&limit));
        }
        let boundary: Vec<_> = self
            .dimensions
            .iter()
            .map(|dimension| dimension.eq(&limit))
            .collect();
        self.solver.assert(Bool::or(&boundary));
    }

    fn environment_from_model(&self, model: &z3::Model) -> Result<Environment, ShapeError> {
        let mut environment = Environment {
            equalities: self.known_equalities.clone(),
            ..Environment::default()
        };
        for (variable, shape) in &self.variable_types {
            let ty = concrete_type(model, shape)?;
            environment.types.insert(variable.clone(), ty);
        }
        for (expression, projection) in &self.projections {
            environment
                .equalities
                .insert(expression.clone(), model_u64(model, projection)?);
        }
        Ok(environment)
    }
}

impl Iterator for EnvironmentIterator {
    type Item = Result<Environment, ShapeError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        if self.dimensions.is_empty() {
            if self.dimensionless_yielded {
                self.finished = true;
                return None;
            }
            self.dimensionless_yielded = true;
            return Some(
                self.environment_from_model(
                    &self
                        .solver
                        .get_model()
                        .expect("satisfiable solver must have a model"),
                ),
            );
        }

        loop {
            match self.solver.check() {
                SatResult::Sat => {
                    let model = self
                        .solver
                        .get_model()
                        .expect("satisfiable solver must have a model");
                    let environment = match self.environment_from_model(&model) {
                        Ok(environment) => environment,
                        Err(error) => {
                            self.finished = true;
                            return Some(Err(error));
                        }
                    };
                    let blocker: Vec<_> = self
                        .dimensions
                        .iter()
                        .chain(self.projections.iter().map(|(_, value)| value))
                        .map(|dimension| {
                            let value = model
                                .eval(dimension, false)
                                .expect("environment dimension must have a model value");
                            dimension.eq(value).not()
                        })
                        .collect();
                    self.solver.assert(Bool::or(&blocker));
                    return Some(Ok(environment));
                }
                SatResult::Unsat => {
                    self.solver.pop(1);
                    if self.dim_limit == self.max_dimension {
                        self.finished = true;
                        return None;
                    }
                    self.dim_limit = self.dim_limit.checked_add(1).unwrap();
                    self.push_dim_limit();
                }
                SatResult::Unknown => {
                    self.finished = true;
                    return Some(Err(ShapeError::Unknown(
                        self.solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "unknown reason".to_owned()),
                    )));
                }
            }
        }
    }
}

struct ShapeContext<'a> {
    solver: &'a mut Solver,
    variable_types: &'a BTreeMap<Variable, Shape>,
    projections: &'a mut BTreeMap<Expr<()>, Int>,
}

impl ShapeContext<'_> {
    fn known_equalities(
        &self,
        assumptions: &[Expr<()>],
    ) -> Result<HashMap<Expr<()>, u64>, ShapeError> {
        let mut equalities = HashMap::new();
        for assumption in assumptions {
            let RawExpr::CmpChain(CmpChain { start, assertions }) = &assumption.raw else {
                continue;
            };
            let [(Cmp::Eq, right)] = assertions.as_slice() else {
                continue;
            };
            let pair = match (&start.raw, &right.raw) {
                (_, RawExpr::NatLiteral(value)) if self.lower_nat(start)?.is_some() => {
                    Some((start.clone(), *value))
                }
                (RawExpr::NatLiteral(value), _) if self.lower_nat(right)?.is_some() => {
                    Some((right.clone(), *value))
                }
                _ => None,
            };
            if let Some((expression, value)) = pair
                && let Some(previous) = equalities.insert(expression, value)
                && previous != value
            {
                return Err(ShapeError::Unsat(
                    "a natural expression has conflicting known values".to_owned(),
                ));
            }
        }
        Ok(equalities)
    }

    fn constrain_assertion(&mut self, expression: &Expr<()>) -> Result<(), ShapeError> {
        if let RawExpr::CmpChain(chain) = &expression.raw
            && let Some(comparison) = self.natural_comparison(chain)?
        {
            self.solver.assert(comparison);
        }
        self.infer(expression).map(|_| ())
    }

    fn natural_comparison(&self, chain: &CmpChain<()>) -> Result<Option<Bool>, ShapeError> {
        let Some(mut previous) = self.lower_nat(&chain.start)? else {
            return Ok(None);
        };
        let mut clauses = Vec::new();
        for (comparison, current) in &chain.assertions {
            let Some(current) = self.lower_nat(current)? else {
                return Ok(None);
            };
            clauses.push(compare_int(&previous, *comparison, &current));
            previous = current;
        }
        Ok(Some(Bool::and(&clauses)))
    }

    fn lower_nat(&self, expression: &Expr<()>) -> Result<Option<Int>, ShapeError> {
        match &expression.raw {
            RawExpr::NatLiteral(value) => Ok(Some(Int::from_u64(*value))),
            RawExpr::Variable(variable)
                if matches!(self.variable_types.get(variable), Some(Shape::Nat)) =>
            {
                Ok(Some(Int::new_const(variable_z3_name(variable))))
            }
            RawExpr::Monop(Monop::Neg, inner) if self.lower_nat(inner)?.is_some() => Err(
                ShapeError::Unsupported("natural expressions do not support negation".to_owned()),
            ),
            RawExpr::Finop(Finop::Plus, terms) => {
                let mut lowered = Vec::new();
                for term in terms {
                    let Some(term) = self.lower_nat(term)? else {
                        return Ok(None);
                    };
                    lowered.push(term);
                }
                Ok(Some(Int::add(&lowered)))
            }
            RawExpr::Finop(Finop::Times, factors) => {
                let mut coefficient = 1u64;
                let mut symbolic = None;
                for factor in factors {
                    if let Some(value) = natural_literal(factor) {
                        coefficient = coefficient.checked_mul(value).ok_or_else(|| {
                            ShapeError::Unsupported("linear coefficient overflow".to_owned())
                        })?;
                    } else if symbolic.is_none() {
                        symbolic = self.lower_nat(factor)?;
                        if symbolic.is_none() {
                            return Ok(None);
                        }
                    } else {
                        return Err(ShapeError::Unsupported(
                            "symbolic multiplication is not Presburger arithmetic".to_owned(),
                        ));
                    }
                }
                Ok(Some(match symbolic {
                    Some(value) => value * Int::from_u64(coefficient),
                    None => Int::from_u64(coefficient),
                }))
            }
            _ => Ok(None),
        }
    }

    fn infer(&mut self, expression: &Expr<()>) -> Result<Shape, ShapeError> {
        match &expression.raw {
            RawExpr::Hole | RawExpr::Type(_) => Ok(Shape::Bool),
            RawExpr::Variable(variable) => {
                self.variable_types.get(variable).cloned().ok_or_else(|| {
                    ShapeError::InvalidTyping(format!(
                        "missing inferred type for {}",
                        variable_z3_name(variable)
                    ))
                })
            }
            RawExpr::NatLiteral(_) => Ok(Shape::Nat),
            RawExpr::Matrix(matrix) => {
                for element in &matrix.elements {
                    if matches!(self.infer(element)?, Shape::Matrix(_, _)) {
                        return Err(ShapeError::Unsupported(
                            "block matrix shape inference is not supported".to_owned(),
                        ));
                    }
                }
                Ok(Shape::Matrix(
                    Int::from_u64(matrix.rows as u64),
                    Int::from_u64(matrix.cols as u64),
                ))
            }
            RawExpr::Monop(op, inner) => {
                let shape = self.infer(inner)?;
                match (op, shape) {
                    (Monop::Transpose, Shape::Matrix(rows, cols)) => Ok(Shape::Matrix(cols, rows)),
                    (Monop::Inverse, Shape::Matrix(rows, cols)) => {
                        self.solver.assert(rows.eq(&cols));
                        Ok(Shape::Matrix(rows, cols))
                    }
                    (Monop::Trace | Monop::Det, Shape::Matrix(rows, cols)) => {
                        self.solver.assert(rows.eq(cols));
                        Ok(Shape::Real)
                    }
                    (Monop::Norm1 | Monop::Norm2 | Monop::NormInfty | Monop::NormFrob, _) => {
                        Ok(Shape::Real)
                    }
                    (_, shape) => Ok(shape),
                }
            }
            RawExpr::Binop(Binop::ElementOf, left, right) => self.constrain_membership(left, right),
            RawExpr::Binop(Binop::SingleSubscript, left, index) => {
                let Shape::Seq(element, _) = self.infer(left)? else {
                    return Err(ShapeError::InvalidTyping(
                        "subscripted expression is not a sequence".to_owned(),
                    ));
                };
                if !matches!(index.raw, RawExpr::Variable(_) | RawExpr::NatLiteral(_))
                    && self.lower_nat(index)?.is_none()
                {
                    return Err(ShapeError::InvalidTyping(
                        "sequence index must be natural-number arithmetic".to_owned(),
                    ));
                }
                Ok(*element)
            }
            RawExpr::Binop(Binop::Power, base, exponent) => {
                self.infer(exponent)?;
                let shape = self.infer(base)?;
                if let Shape::Matrix(rows, cols) = &shape {
                    self.solver.assert(rows.eq(cols));
                }
                Ok(shape)
            }
            RawExpr::Binop(Binop::Div, left, right) => {
                let left = self.infer(left)?;
                let left = self.division_scalar(left);
                let right = self.infer(right)?;
                let right = self.division_scalar(right);
                scalar_shape_lub(left, right)
            }
            RawExpr::Binop(_, left, right) => {
                self.infer(left)?;
                self.infer(right)?;
                Ok(Shape::Real)
            }
            RawExpr::Finop(Finop::Plus, expressions) => {
                let (first, rest) = expressions
                    .split_first()
                    .ok_or_else(|| ShapeError::InvalidTyping("empty addition".to_owned()))?;
                let mut result = self.infer(first)?;
                for expression in rest {
                    let shape = self.infer(expression)?;
                    result = self.add_shapes(result, shape)?;
                }
                Ok(result)
            }
            RawExpr::Finop(Finop::Times, expressions) => {
                let (first, rest) = expressions
                    .split_first()
                    .ok_or_else(|| ShapeError::InvalidTyping("empty multiplication".to_owned()))?;
                let mut result = self.infer(first)?;
                for expression in rest {
                    let shape = self.infer(expression)?;
                    result = self.multiply_shapes(result, shape)?;
                }
                Ok(result)
            }
            RawExpr::CmpChain(chain) => {
                let mut previous = self.infer(&chain.start)?;
                for (_, current) in &chain.assertions {
                    let current = self.infer(current)?;
                    self.equal_shapes(&previous, &current);
                    previous = current;
                }
                Ok(Shape::Bool)
            }
            RawExpr::LogicChain(chain) => {
                self.infer(&chain.start)?;
                for (_, expression) in &chain.assertions {
                    self.infer(expression)?;
                }
                Ok(Shape::Bool)
            }
            RawExpr::Seqop(op, range, body) => {
                let from = self.lower_nat(&range.from)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "sequence lower bound is not linear natural arithmetic".to_owned(),
                    )
                })?;
                let to = self.lower_nat(&range.to)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "sequence upper bound is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.solver.assert(from.ge(1));
                self.solver.assert(from.le(&to));
                let lengths =
                    indexed_sequence_lengths(body, &range.index_variable, self.variable_types)?;
                if lengths.is_empty() {
                    return Err(ShapeError::InvalidTyping(
                        "sequence operation body does not index a sequence".to_owned(),
                    ));
                }
                for length in lengths {
                    self.solver.assert(to.le(length));
                }
                self.projections.insert(range.from.clone(), from);
                self.projections.insert(range.to.clone(), to);
                let shape = self.infer(body)?;
                if matches!(op, SeqOp::Prod)
                    && let Shape::Matrix(rows, cols) = &shape
                {
                    self.solver.assert(rows.eq(cols));
                }
                Ok(shape)
            }
            RawExpr::Triop(_, _, _, _) | RawExpr::Finop(_, _) => Err(ShapeError::Unsupported(
                "expression has unsupported shape semantics".to_owned(),
            )),
        }
    }

    fn constrain_membership(
        &mut self,
        left: &Expr<()>,
        right: &Expr<()>,
    ) -> Result<Shape, ShapeError> {
        let RawExpr::Variable(variable) = &left.raw else {
            return Err(ShapeError::InvalidTyping(
                "type membership requires a variable subject".to_owned(),
            ));
        };
        let RawExpr::Type(ty) = &right.raw else {
            return Err(ShapeError::InvalidTyping(
                "type membership requires a type expression".to_owned(),
            ));
        };
        let actual = self.variable_types.get(variable).ok_or_else(|| {
            ShapeError::InvalidTyping("membership subject has no inferred type".to_owned())
        })?;
        match (actual, ty) {
            (Shape::Bool, TypeExpr::Bool)
            | (Shape::Nat, TypeExpr::Nat)
            | (Shape::Int, TypeExpr::Int)
            | (Shape::Real, TypeExpr::Real) => {}
            (Shape::Matrix(rows, cols), TypeExpr::Matrix(expected_rows, expected_cols)) => {
                let row_value = self.lower_nat(expected_rows)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix row dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                let col_value = self.lower_nat(expected_cols)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix column dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.projections
                    .insert(expected_rows.clone(), row_value.clone());
                self.projections
                    .insert(expected_cols.clone(), col_value.clone());
                self.solver.assert(rows.eq(row_value));
                self.solver.assert(cols.eq(col_value));
            }
            (Shape::Seq(element, length), TypeExpr::Seq(expected_element, expected_length)) => {
                let RawExpr::Type(expected_element) = &expected_element.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "sequence element must be a type expression".to_owned(),
                    ));
                };
                let length_value = self.lower_nat(expected_length)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "sequence length is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.projections
                    .insert(expected_length.clone(), length_value.clone());
                self.solver.assert(length.eq(length_value));
                self.constrain_shape_type(element, expected_element)?;
            }
            _ => self.solver.assert(Bool::from_bool(false)),
        }
        Ok(Shape::Bool)
    }

    fn constrain_shape_type(
        &mut self,
        actual: &Shape,
        expected: &TypeExpr<()>,
    ) -> Result<(), ShapeError> {
        match (actual, expected) {
            (Shape::Bool, TypeExpr::Bool)
            | (Shape::Nat, TypeExpr::Nat)
            | (Shape::Int, TypeExpr::Int)
            | (Shape::Real, TypeExpr::Real) => Ok(()),
            (Shape::Matrix(rows, cols), TypeExpr::Matrix(expected_rows, expected_cols)) => {
                let row_value = self.lower_nat(expected_rows)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix row dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                let col_value = self.lower_nat(expected_cols)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix column dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.projections
                    .insert(expected_rows.clone(), row_value.clone());
                self.projections
                    .insert(expected_cols.clone(), col_value.clone());
                self.solver.assert(rows.eq(row_value));
                self.solver.assert(cols.eq(col_value));
                Ok(())
            }
            (Shape::Seq(_, _), TypeExpr::Seq(_, _)) => Err(ShapeError::Unsupported(
                "nested sequence constraints are not supported".to_owned(),
            )),
            _ => {
                self.solver.assert(Bool::from_bool(false));
                Ok(())
            }
        }
    }

    fn add_shapes(&mut self, left: Shape, right: Shape) -> Result<Shape, ShapeError> {
        match (&left, &right) {
            (Shape::Matrix(lr, lc), Shape::Matrix(rr, rc)) => {
                self.solver.assert(lr.eq(rr));
                self.solver.assert(lc.eq(rc));
                Ok(left)
            }
            (Shape::Matrix(_, _), _) | (_, Shape::Matrix(_, _)) => {
                self.solver.assert(Bool::from_bool(false));
                Ok(left)
            }
            _ => scalar_shape_lub(left, right),
        }
    }

    fn multiply_shapes(&mut self, left: Shape, right: Shape) -> Result<Shape, ShapeError> {
        match (left, right) {
            (Shape::Matrix(rows, inner), Shape::Matrix(right_inner, cols)) => {
                self.solver.assert(inner.eq(right_inner));
                Ok(Shape::Matrix(rows, cols))
            }
            (matrix @ Shape::Matrix(_, _), scalar) | (scalar, matrix @ Shape::Matrix(_, _)) => {
                require_scalar(&scalar)?;
                Ok(matrix)
            }
            (left, right) => scalar_shape_lub(left, right),
        }
    }

    fn equal_shapes(&mut self, left: &Shape, right: &Shape) {
        match (left, right) {
            (Shape::Matrix(lr, lc), Shape::Matrix(rr, rc)) => {
                self.solver.assert(lr.eq(rr));
                self.solver.assert(lc.eq(rc));
            }
            (Shape::Matrix(rows, cols), scalar) | (scalar, Shape::Matrix(rows, cols)) => {
                if require_scalar(scalar).is_ok() {
                    self.solver.assert(rows.eq(1));
                    self.solver.assert(cols.eq(1));
                } else {
                    self.solver.assert(Bool::from_bool(false));
                }
            }
            _ => {}
        }
    }

    fn division_scalar(&mut self, shape: Shape) -> Shape {
        match shape {
            Shape::Matrix(rows, cols) => {
                self.solver.assert(rows.eq(1));
                self.solver.assert(cols.eq(1));
                Shape::Real
            }
            shape => shape,
        }
    }
}

fn scalar_shape(ty: &TypeExpr<()>) -> Option<Shape> {
    Some(match ty {
        TypeExpr::Bool => Shape::Bool,
        TypeExpr::Nat => Shape::Nat,
        TypeExpr::Int => Shape::Int,
        TypeExpr::Real => Shape::Real,
        TypeExpr::Matrix(_, _) | TypeExpr::Seq(_, _) => return None,
    })
}

fn shape_from_type_expr(
    variable: &Variable,
    ty: &TypeExpr<()>,
    generated_names: &mut BTreeSet<String>,
) -> Result<Shape, ShapeError> {
    if let Some(shape) = scalar_shape(ty) {
        return Ok(shape);
    }
    match ty {
        TypeExpr::Matrix(_, _) => Ok(matrix_shape(variable, generated_names)),
        TypeExpr::Seq(element, _) => {
            let RawExpr::Type(element) = &element.raw else {
                return Err(ShapeError::InvalidTyping(
                    "sequence element must be a type expression".to_owned(),
                ));
            };
            if matches!(element, TypeExpr::Seq(_, _)) {
                return Err(ShapeError::Unsupported(
                    "nested sequence inference is not supported".to_owned(),
                ));
            }
            let element =
                shape_from_type_expr_with_prefix(variable, element, "element_", generated_names)?;
            Ok(Shape::Seq(
                Box::new(element),
                dimension_for(variable, "length", generated_names),
            ))
        }
        _ => unreachable!(),
    }
}

fn shape_from_type_expr_with_prefix(
    variable: &Variable,
    ty: &TypeExpr<()>,
    prefix: &str,
    generated_names: &mut BTreeSet<String>,
) -> Result<Shape, ShapeError> {
    if let Some(shape) = scalar_shape(ty) {
        return Ok(shape);
    }
    match ty {
        TypeExpr::Matrix(_, _) => Ok(Shape::Matrix(
            dimension_for(variable, &format!("{prefix}rows"), generated_names),
            dimension_for(variable, &format!("{prefix}cols"), generated_names),
        )),
        TypeExpr::Seq(_, _) => Err(ShapeError::Unsupported(
            "nested sequence inference is not supported".to_owned(),
        )),
        _ => unreachable!(),
    }
}

fn shape_dimensions(shape: &Shape) -> Vec<Int> {
    match shape {
        Shape::Matrix(rows, cols) => vec![rows.clone(), cols.clone()],
        Shape::Seq(element, length) => {
            let mut dimensions = vec![length.clone()];
            dimensions.extend(shape_dimensions(element));
            dimensions
        }
        _ => Vec::new(),
    }
}

fn concrete_type(model: &z3::Model, shape: &Shape) -> Result<Type, ShapeError> {
    Ok(match shape {
        Shape::Bool => Type::Bool,
        Shape::Nat => Type::Nat,
        Shape::Int => Type::Int,
        Shape::Real => Type::Real,
        Shape::Matrix(rows, cols) => Type::Matrix(model_u64(model, rows)?, model_u64(model, cols)?),
        Shape::Seq(element, length) => Type::Seq(Box::new(SeqType {
            t: concrete_type(model, element)?,
            n: model_u64(model, length)?,
        })),
    })
}

fn indexed_sequence_lengths(
    expression: &Expr<()>,
    index: &Variable,
    variable_types: &BTreeMap<Variable, Shape>,
) -> Result<Vec<Int>, ShapeError> {
    let mut lengths = BTreeMap::new();
    collect_indexed_sequence_lengths(expression, index, variable_types, &mut lengths)?;
    Ok(lengths.into_values().collect())
}

fn collect_indexed_sequence_lengths(
    expression: &Expr<()>,
    index: &Variable,
    variable_types: &BTreeMap<Variable, Shape>,
    lengths: &mut BTreeMap<Variable, Int>,
) -> Result<(), ShapeError> {
    match &expression.raw {
        RawExpr::Binop(Binop::SingleSubscript, base, subscript) if matches!(&subscript.raw, RawExpr::Variable(variable) if variable == index) =>
        {
            let RawExpr::Variable(variable) = &base.raw else {
                return Err(ShapeError::Unsupported(
                    "sequence subscript base must be a variable".to_owned(),
                ));
            };
            let Some(Shape::Seq(_, length)) = variable_types.get(variable) else {
                return Err(ShapeError::InvalidTyping(
                    "subscripted variable is not a sequence".to_owned(),
                ));
            };
            lengths.insert(variable.clone(), length.clone());
        }
        RawExpr::Type(_) | RawExpr::Hole | RawExpr::Variable(_) | RawExpr::NatLiteral(_) => {}
        RawExpr::Matrix(matrix) => {
            for element in &matrix.elements {
                collect_indexed_sequence_lengths(element, index, variable_types, lengths)?;
            }
        }
        RawExpr::Monop(_, inner) => {
            collect_indexed_sequence_lengths(inner, index, variable_types, lengths)?
        }
        RawExpr::Binop(_, left, right) => {
            collect_indexed_sequence_lengths(left, index, variable_types, lengths)?;
            collect_indexed_sequence_lengths(right, index, variable_types, lengths)?;
        }
        RawExpr::Triop(_, first, second, third) => {
            for expression in [first, second, third] {
                collect_indexed_sequence_lengths(expression, index, variable_types, lengths)?;
            }
        }
        RawExpr::Finop(_, expressions) => {
            for expression in expressions {
                collect_indexed_sequence_lengths(expression, index, variable_types, lengths)?;
            }
        }
        RawExpr::CmpChain(chain) => {
            collect_indexed_sequence_lengths(&chain.start, index, variable_types, lengths)?;
            for (_, expression) in &chain.assertions {
                collect_indexed_sequence_lengths(expression, index, variable_types, lengths)?;
            }
        }
        RawExpr::LogicChain(chain) => {
            collect_indexed_sequence_lengths(&chain.start, index, variable_types, lengths)?;
            for (_, expression) in &chain.assertions {
                collect_indexed_sequence_lengths(expression, index, variable_types, lengths)?;
            }
        }
        RawExpr::Seqop(_, _, _) => {
            return Err(ShapeError::Unsupported(
                "nested sequence operations are not supported".to_owned(),
            ));
        }
    }
    Ok(())
}

fn guessed_shape(variable: &Variable, generated_names: &mut BTreeSet<String>) -> Shape {
    let first = variable.name.chars().next().unwrap_or('_');
    if first.is_ascii_uppercase() {
        matrix_shape(variable, generated_names)
    } else if matches!(variable.name.as_str(), "u" | "v" | "w" | "x" | "y" | "z") {
        let rows = dimension_for(variable, "rows", generated_names);
        Shape::Matrix(rows, Int::from_u64(1))
    } else if matches!(variable.name.as_str(), "n" | "i" | "j" | "k" | "l" | "m") {
        Shape::Nat
    } else {
        Shape::Real
    }
}

fn matrix_shape(variable: &Variable, generated_names: &mut BTreeSet<String>) -> Shape {
    Shape::Matrix(
        dimension_for(variable, "rows", generated_names),
        dimension_for(variable, "cols", generated_names),
    )
}

fn dimension_for(variable: &Variable, axis: &str, generated_names: &mut BTreeSet<String>) -> Int {
    let name = format!("{}_{{{axis}}}", variable_z3_name(variable));
    generated_names.insert(name.clone());
    Int::new_const(name)
}

fn variable_z3_name(variable: &Variable) -> String {
    variable.z3_name()
}

fn collect_variables(expression: &Expr<()>, variables: &mut BTreeSet<Variable>) {
    collect_variables_bound(expression, variables, &BTreeSet::new());
}

fn collect_variables_bound(
    expression: &Expr<()>,
    variables: &mut BTreeSet<Variable>,
    bound: &BTreeSet<Variable>,
) {
    match &expression.raw {
        RawExpr::Variable(variable) => {
            if !bound.contains(variable) {
                variables.insert(variable.clone());
            }
        }
        RawExpr::Type(ty) => collect_type_dimension_variables(ty, variables),
        RawExpr::Matrix(matrix) => {
            for expression in &matrix.elements {
                collect_variables_bound(expression, variables, bound);
            }
        }
        RawExpr::Monop(_, expression) => collect_variables_bound(expression, variables, bound),
        RawExpr::Binop(_, left, right) => {
            collect_variables_bound(left, variables, bound);
            collect_variables_bound(right, variables, bound);
        }
        RawExpr::Triop(_, first, second, third) => {
            collect_variables_bound(first, variables, bound);
            collect_variables_bound(second, variables, bound);
            collect_variables_bound(third, variables, bound);
        }
        RawExpr::Finop(_, expressions) => {
            for expression in expressions {
                collect_variables_bound(expression, variables, bound);
            }
        }
        RawExpr::CmpChain(chain) => {
            collect_variables_bound(&chain.start, variables, bound);
            for (_, expression) in &chain.assertions {
                collect_variables_bound(expression, variables, bound);
            }
        }
        RawExpr::LogicChain(chain) => {
            collect_variables_bound(&chain.start, variables, bound);
            for (_, expression) in &chain.assertions {
                collect_variables_bound(expression, variables, bound);
            }
        }
        RawExpr::Seqop(_, range, body) => {
            collect_variables_bound(&range.from, variables, bound);
            collect_variables_bound(&range.to, variables, bound);
            let mut body_bound = bound.clone();
            body_bound.insert(range.index_variable.clone());
            collect_variables_bound(body, variables, &body_bound);
        }
        RawExpr::Hole | RawExpr::NatLiteral(_) => {}
    }
}

fn collect_type_dimension_variables(ty: &TypeExpr<()>, variables: &mut BTreeSet<Variable>) {
    match ty {
        TypeExpr::Matrix(rows, cols) => {
            collect_variables(rows, variables);
            collect_variables(cols, variables);
        }
        TypeExpr::Seq(element, size) => {
            collect_variables(element, variables);
            collect_variables(size, variables);
        }
        _ => {}
    }
}

fn collect_range_bound_variables(expression: &Expr<()>, variables: &mut BTreeSet<Variable>) {
    match &expression.raw {
        RawExpr::Seqop(_, range, body) => {
            collect_variables(&range.from, variables);
            collect_variables(&range.to, variables);
            collect_range_bound_variables(body, variables);
        }
        RawExpr::Matrix(matrix) => {
            for element in &matrix.elements {
                collect_range_bound_variables(element, variables);
            }
        }
        RawExpr::Monop(_, inner) => collect_range_bound_variables(inner, variables),
        RawExpr::Binop(_, left, right) => {
            collect_range_bound_variables(left, variables);
            collect_range_bound_variables(right, variables);
        }
        RawExpr::Triop(_, first, second, third) => {
            collect_range_bound_variables(first, variables);
            collect_range_bound_variables(second, variables);
            collect_range_bound_variables(third, variables);
        }
        RawExpr::Finop(_, expressions) => {
            for expression in expressions {
                collect_range_bound_variables(expression, variables);
            }
        }
        RawExpr::CmpChain(chain) => {
            collect_range_bound_variables(&chain.start, variables);
            for (_, expression) in &chain.assertions {
                collect_range_bound_variables(expression, variables);
            }
        }
        RawExpr::LogicChain(chain) => {
            collect_range_bound_variables(&chain.start, variables);
            for (_, expression) in &chain.assertions {
                collect_range_bound_variables(expression, variables);
            }
        }
        RawExpr::Type(_) | RawExpr::Hole | RawExpr::Variable(_) | RawExpr::NatLiteral(_) => {}
    }
}

fn natural_literal(expression: &Expr<()>) -> Option<u64> {
    match &expression.raw {
        RawExpr::NatLiteral(value) => Some(*value),
        _ => None,
    }
}

fn scalar_shape_lub(left: Shape, right: Shape) -> Result<Shape, ShapeError> {
    match (left, right) {
        (Shape::Bool, _) | (_, Shape::Bool) => Err(ShapeError::InvalidTyping(
            "Boolean values are not numeric scalars".to_owned(),
        )),
        (Shape::Matrix(_, _), _) | (_, Shape::Matrix(_, _)) => Err(ShapeError::InvalidTyping(
            "matrix values are not scalar operands".to_owned(),
        )),
        (Shape::Seq(_, _), _) | (_, Shape::Seq(_, _)) => Err(ShapeError::InvalidTyping(
            "sequence values are not scalar operands".to_owned(),
        )),
        (Shape::Real, _) | (_, Shape::Real) => Ok(Shape::Real),
        (Shape::Int, _) | (_, Shape::Int) => Ok(Shape::Int),
        (Shape::Nat, Shape::Nat) => Ok(Shape::Nat),
    }
}

fn require_scalar(shape: &Shape) -> Result<(), ShapeError> {
    if matches!(shape, Shape::Bool | Shape::Matrix(_, _) | Shape::Seq(_, _)) {
        Err(ShapeError::InvalidTyping(
            "operation requires a numeric scalar".to_owned(),
        ))
    } else {
        Ok(())
    }
}

fn compare_int(left: &Int, comparison: Cmp, right: &Int) -> Bool {
    match comparison {
        Cmp::Eq => left.eq(right),
        Cmp::Ne => left.eq(right).not(),
        Cmp::Lt => left.lt(right),
        Cmp::Gt => left.gt(right),
        Cmp::Le => left.le(right),
        Cmp::Ge => left.ge(right),
    }
}

fn model_u64(model: &z3::Model, expression: &Int) -> Result<u64, ShapeError> {
    model
        .eval(expression, false)
        .and_then(|value| value.as_u64())
        .ok_or_else(|| {
            ShapeError::Unknown("matrix dimension has no unsigned model value".to_owned())
        })
}

#[cfg(test)]
mod tests {
    use ratex_parser::parse;

    use super::{ShapeError, extract_environment_iterator};
    use crate::{Annotation, Expr, Matrix, RawExpr, SeqType, Type, Variable, from_tex};

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
    }

    fn environments(tex: &[&str]) -> super::EnvironmentIterator {
        extract_environment_iterator(tex.iter().map(|tex| expression(tex)), 10).unwrap()
    }

    #[test]
    fn guesses_types_and_respects_explicit_type_assertions() {
        let environment = environments(&[r"a = a", r"n = n", r"x \in \mathbb{R}"])
            .next()
            .unwrap()
            .unwrap();
        assert_eq!(environment.types[&Variable::new("a")], Type::Real);
        assert_eq!(environment.types[&Variable::new("n")], Type::Nat);
        assert_eq!(environment.types[&Variable::new("x")], Type::Real);
    }

    #[test]
    fn enumerates_by_increasing_dimension_limit() {
        let mut environments = environments(&[r"A \in \mathbb{R}^{n \times d + p}"]);
        let first = environments.next().unwrap().unwrap();
        assert_eq!(first.types[&Variable::new("A")], Type::Matrix(1, 1));

        let next_limit: Vec<_> = environments
            .take(3)
            .map(|result| {
                let environment = result.unwrap();
                environment.types[&Variable::new("A")].clone()
            })
            .collect();
        assert_eq!(next_limit.len(), 3);
        assert!(
            next_limit
                .iter()
                .all(|ty| matches!(ty, Type::Matrix(rows, cols) if (*rows).max(*cols) == 2))
        );
    }

    #[test]
    fn enumerates_sequence_lengths_and_element_dimensions() {
        let z = Variable {
            name: "z".to_owned(),
            non_numeric_subscript: String::new(),
            annotations: vec![Annotation::Arrow],
        };
        let environments: Vec<_> = extract_environment_iterator(
            [expression(
                r"\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})",
            )]
            .into_iter(),
            2,
        )
        .unwrap()
        .map(Result::unwrap)
        .collect();
        let types: Vec<_> = environments
            .iter()
            .map(|environment| environment.types[&z].clone())
            .collect();
        assert_eq!(types.len(), 4);
        assert!(types.contains(&Type::Seq(Box::new(SeqType {
            t: Type::Matrix(1, 1),
            n: 1,
        }))));
        assert!(types.contains(&Type::Seq(Box::new(SeqType {
            t: Type::Matrix(2, 1),
            n: 2,
        }))));
    }

    #[test]
    fn enumerates_each_admissible_sequence_subrange() {
        let z = Variable {
            name: "z".to_owned(),
            non_numeric_subscript: String::new(),
            annotations: vec![Annotation::Arrow],
        };
        let assumptions = [
            expression(r"\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R})"),
            expression(r"\sum_{i=a}^{b} \vec{z}_i = 0"),
        ];
        let environments: Vec<_> = extract_environment_iterator(assumptions.into_iter(), 2)
            .unwrap()
            .map(Result::unwrap)
            .collect();
        let ranges: Vec<_> = environments
            .iter()
            .map(|environment| {
                (
                    environment.equalities[&expression("a")],
                    environment.equalities[&expression("b")],
                    match &environment.types[&z] {
                        Type::Seq(sequence) => sequence.n,
                        _ => panic!("expected a sequence"),
                    },
                )
            })
            .collect();
        assert_eq!(ranges.len(), 4);
        assert!(ranges.contains(&(1, 1, 1)));
        assert!(ranges.contains(&(1, 1, 2)));
        assert!(ranges.contains(&(1, 2, 2)));
        assert!(ranges.contains(&(2, 2, 2)));
    }

    #[test]
    fn stops_after_the_maximum_dimension() {
        let environments: Vec<_> =
            extract_environment_iterator([expression("A = A")].into_iter(), 2)
                .unwrap()
                .map(Result::unwrap)
                .collect();
        assert_eq!(environments.len(), 4);
        assert!(environments.iter().all(|environment| {
            matches!(environment.types[&Variable::new("A")], Type::Matrix(rows, cols) if rows <= 2 && cols <= 2)
        }));
    }

    #[test]
    fn zero_bound_excludes_matrices_but_not_dimensionless_environments() {
        assert_eq!(
            extract_environment_iterator([expression("A = A")].into_iter(), 0)
                .unwrap()
                .count(),
            0
        );
        assert_eq!(
            extract_environment_iterator([expression("a = a")].into_iter(), 0)
                .unwrap()
                .count(),
            1
        );
    }

    #[test]
    fn auxiliary_naturals_do_not_duplicate_environments() {
        let types: Vec<_> = environments(&[r"A \in \mathbb{R}^{n}", r"p = p"])
            .take(3)
            .map(|result| result.unwrap().types[&Variable::new("A")].clone())
            .collect();
        assert_eq!(
            types,
            vec![Type::Matrix(1, 1), Type::Matrix(2, 1), Type::Matrix(3, 1)]
        );
    }

    #[test]
    fn implicit_matrix_constraints_restrict_environments() {
        let environment =
            environments(&[r"A B = \begin{bmatrix}1 & 2 & 3 \\ 4 & 5 & 6\end{bmatrix}"])
                .next()
                .unwrap()
                .unwrap();
        let Type::Matrix(a_rows, a_cols) = environment.types[&Variable::new("A")] else {
            panic!()
        };
        let Type::Matrix(b_rows, b_cols) = environment.types[&Variable::new("B")] else {
            panic!()
        };
        assert_eq!(a_rows, 2);
        assert_eq!(b_cols, 3);
        assert_eq!(a_cols, b_rows);
    }

    #[test]
    fn natural_assertions_restrict_dimensions() {
        let environment = environments(&[r"A \in \mathbb{R}^{n}", r"n \ge 3"])
            .next()
            .unwrap()
            .unwrap();
        assert_eq!(environment.types[&Variable::new("A")], Type::Matrix(3, 1));
    }

    #[test]
    fn preserves_known_natural_equalities_in_environments() {
        let environment = environments(&[r"k = 2"]).next().unwrap().unwrap();
        assert_eq!(environment.equalities[&expression("k")], 2);
    }

    #[test]
    fn rejects_unsatisfiable_and_nonlinear_constraints() {
        assert!(matches!(
            extract_environment_iterator([expression(r"n < 0")].into_iter(), 10),
            Err(ShapeError::Unsat(_))
        ));
        assert!(matches!(
            extract_environment_iterator([expression(r"A \in \mathbb{R}^{n p}")].into_iter(), 10),
            Err(ShapeError::Unsupported(_))
        ));
        assert!(matches!(
            extract_environment_iterator([expression(r"A \in \mathbb{R}^{-n}")].into_iter(), 10),
            Err(ShapeError::Unsupported(_))
        ));
    }

    #[test]
    fn rejects_generated_dimension_name_collisions() {
        assert!(matches!(
            extract_environment_iterator(
                [expression(r"A = A"), expression(r"A_{rows} = A_{rows}"),].into_iter(),
                10,
            ),
            Err(ShapeError::InvalidTyping(_))
        ));
    }

    #[test]
    fn rejects_block_matrices_until_their_shapes_are_supported() {
        let scalar: Expr<()> = Expr::new(RawExpr::NatLiteral(1));
        let block = Expr::new(RawExpr::Matrix(Matrix {
            rows: 1,
            cols: 1,
            elements: vec![scalar],
        }));
        let matrix = Expr::new(RawExpr::Matrix(Matrix {
            rows: 1,
            cols: 1,
            elements: vec![block],
        }));
        assert!(matches!(
            extract_environment_iterator([matrix].into_iter(), 10),
            Err(ShapeError::Unsupported(_))
        ));
    }

    #[test]
    fn rejects_boolean_numeric_operations() {
        assert!(matches!(
            extract_environment_iterator(
                [expression(r"b \in \mathbb{B}"), expression("b + 1 = 2")].into_iter(),
                10,
            ),
            Err(ShapeError::InvalidTyping(_))
        ));
    }
}
