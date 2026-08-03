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
    Binop, Cmp, CmpChain, Environment, Expr, Finop, Monop, RawExpr, Type, TypeExpr, Variable,
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
}

pub struct EnvironmentIterator {
    solver: Solver,
    variable_types: BTreeMap<Variable, Shape>,
    dimensions: Vec<Int>,
    known_equalities: HashMap<Expr<()>, u64>,
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
    let known_equalities = {
        let mut context = ShapeContext {
            solver: &mut solver,
            variable_types: &variable_types,
        };
        for assumption in &assumptions {
            context.constrain_assertion(assumption)?;
        }
        context.known_equalities(&assumptions)?
    };
    check_base_constraints(&mut solver)?;

    let dimensions: Vec<Int> = variable_types
        .values()
        .filter_map(|shape| match shape {
            Shape::Matrix(rows, cols) => Some([rows.clone(), cols.clone()]),
            _ => None,
        })
        .flatten()
        .collect();
    let finished = !dimensions.is_empty() && max_dimension == 0;
    let mut iterator = EnvironmentIterator {
        solver,
        variable_types,
        dimensions,
        known_equalities,
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
            scalar_shape(ty).unwrap_or_else(|| matrix_shape(&variable, &mut generated_names))
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
        if let Shape::Matrix(rows, cols) = shape {
            solver.assert(rows.gt(0));
            solver.assert(cols.gt(0));
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
            let ty = match shape {
                Shape::Bool => Type::Bool,
                Shape::Nat => Type::Nat,
                Shape::Int => Type::Int,
                Shape::Real => Type::Real,
                Shape::Matrix(rows, cols) => {
                    Type::Matrix(model_u64(model, rows)?, model_u64(model, cols)?)
                }
            };
            environment.types.insert(variable.clone(), ty);
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
            RawExpr::Triop(_, _, _, _) | RawExpr::Finop(_, _) | RawExpr::Seqop(_, _, _) => Err(
                ShapeError::Unsupported("expression has unsupported shape semantics".to_owned()),
            ),
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
                let expected_rows = self.lower_nat(expected_rows)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix row dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                let expected_cols = self.lower_nat(expected_cols)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "matrix column dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.solver.assert(rows.eq(expected_rows));
                self.solver.assert(cols.eq(expected_cols));
            }
            _ => self.solver.assert(Bool::from_bool(false)),
        }
        Ok(Shape::Bool)
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
            (Shape::Matrix(_, _), _) | (_, Shape::Matrix(_, _)) => {
                self.solver.assert(Bool::from_bool(false))
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
        TypeExpr::Matrix(_, _) => return None,
    })
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
    match &expression.raw {
        RawExpr::Variable(variable) => {
            variables.insert(variable.clone());
        }
        RawExpr::Type(ty) => collect_type_dimension_variables(ty, variables),
        RawExpr::Matrix(matrix) => {
            for expression in &matrix.elements {
                collect_variables(expression, variables);
            }
        }
        RawExpr::Monop(_, expression) => collect_variables(expression, variables),
        RawExpr::Binop(_, left, right) => {
            collect_variables(left, variables);
            collect_variables(right, variables);
        }
        RawExpr::Triop(_, first, second, third) => {
            collect_variables(first, variables);
            collect_variables(second, variables);
            collect_variables(third, variables);
        }
        RawExpr::Finop(_, expressions) => {
            for expression in expressions {
                collect_variables(expression, variables);
            }
        }
        RawExpr::CmpChain(chain) => {
            collect_variables(&chain.start, variables);
            for (_, expression) in &chain.assertions {
                collect_variables(expression, variables);
            }
        }
        RawExpr::LogicChain(chain) => {
            collect_variables(&chain.start, variables);
            for (_, expression) in &chain.assertions {
                collect_variables(expression, variables);
            }
        }
        RawExpr::Seqop(_, range, body) => {
            variables.insert(range.index_variable.clone());
            collect_variables(&range.from, variables);
            collect_variables(&range.to, variables);
            collect_variables(body, variables);
        }
        RawExpr::Hole | RawExpr::NatLiteral(_) => {}
    }
}

fn collect_type_dimension_variables(ty: &TypeExpr<()>, variables: &mut BTreeSet<Variable>) {
    if let TypeExpr::Matrix(rows, cols) = ty {
        collect_variables(rows, variables);
        collect_variables(cols, variables);
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
        (Shape::Real, _) | (_, Shape::Real) => Ok(Shape::Real),
        (Shape::Int, _) | (_, Shape::Int) => Ok(Shape::Int),
        (Shape::Nat, Shape::Nat) => Ok(Shape::Nat),
    }
}

fn require_scalar(shape: &Shape) -> Result<(), ShapeError> {
    if matches!(shape, Shape::Bool | Shape::Matrix(_, _)) {
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
    use crate::{Expr, Matrix, RawExpr, Type, Variable, from_tex};

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
                environment.types[&Variable::new("A")]
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
            .map(|result| result.unwrap().types[&Variable::new("A")])
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
