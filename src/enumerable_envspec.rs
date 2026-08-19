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
    Binop, Cmp, CmpChain, Environment, Expr, Finop, ImplicitDimension, Matrix, Monop, RawExpr,
    SeqOp, SeqType, Type, TypeExpr, Variable, preprocessing::PreparedExpression,
    type_resolver::SymbolicTypeEnvironment,
};

pub fn infer_symbolic_type_environment(
    assumptions: &[Expr<()>],
) -> Result<SymbolicTypeEnvironment, ShapeError> {
    let specification = collect_environment_specification(assumptions)?;
    let mut types = HashMap::new();
    for variable in specification.variables {
        let ty = if specification.dimension_variables.contains(&variable) {
            TypeExpr::Nat
        } else if let Some(ty) = specification
            .explicit_types
            .get(&variable)
            .and_then(|types| types.first())
        {
            ty.clone()
        } else {
            guessed_type_expr(&variable)
        };
        types.insert(variable, ty);
    }
    Ok(SymbolicTypeEnvironment { types })
}

fn guessed_type_expr(variable: &Variable) -> TypeExpr<()> {
    let dimension = |axis: &str| {
        Expr::new(RawExpr::Variable(Variable::new(format!(
            "{}_{{{axis}}}",
            variable.z3_name()
        ))))
    };
    let first = variable.name.chars().next().unwrap_or('_');
    if first.is_ascii_uppercase() {
        TypeExpr::Matrix(dimension("rows"), dimension("cols"))
    } else if matches!(variable.name.as_str(), "u" | "v" | "w" | "x" | "y" | "z") {
        TypeExpr::Matrix(dimension("rows"), Expr::new(RawExpr::NatLiteral(1)))
    } else if matches!(variable.name.as_str(), "n" | "i" | "j" | "k" | "l" | "m") {
        TypeExpr::Nat
    } else {
        TypeExpr::Real
    }
}

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
    implicit_dimensions: Vec<(ImplicitDimension, Int)>,
    dimensions: Vec<Int>,
    known_equalities: HashMap<Expr<()>, u64>,
    projections: Vec<(Expr<()>, Int)>,
    dimension_sum: u64,
    max_dimension_sum: u64,
    dimensionless_yielded: bool,
    finished: bool,
    hidden_variables: BTreeSet<Variable>,
}

pub fn extract_environment_iterator<Metadata>(
    assumptions: impl Iterator<Item = Expr<Metadata>>,
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    extract_environment_iterator_with_context(
        assumptions,
        std::iter::empty::<Expr<()>>(),
        max_dimension,
    )
}

pub fn extract_environment_iterator_with_context<AssumptionMetadata, ContextMetadata>(
    assumptions: impl Iterator<Item = Expr<AssumptionMetadata>>,
    contextual_expressions: impl Iterator<Item = Expr<ContextMetadata>>,
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    extract_environment_iterator_with_hidden(
        assumptions
            .map(|expression| expression.with_default_metadata())
            .collect(),
        contextual_expressions
            .map(|expression| expression.with_default_metadata())
            .collect(),
        max_dimension,
        BTreeSet::new(),
    )
}

pub fn extract_prepared_environment_iterator(
    assumptions: &[PreparedExpression],
    contextual_expressions: &[PreparedExpression],
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    let mut hidden_variables = BTreeSet::new();
    let mut prepared_assumptions = Vec::new();
    let mut prepared_context = Vec::new();
    for prepared in assumptions {
        prepared_assumptions.push(prepared.expression.with_default_metadata());
        append_side_condition_shapes(prepared, &mut prepared_assumptions, &mut hidden_variables);
    }
    for prepared in contextual_expressions {
        prepared_context.push(prepared.expression.with_default_metadata());
        // Generated definitions are typing obligations and must not be skipped by
        // the ordinary-context implicit-nonce filter.
        append_side_condition_shapes(prepared, &mut prepared_assumptions, &mut hidden_variables);
    }
    extract_environment_iterator_with_hidden(
        prepared_assumptions,
        prepared_context,
        max_dimension,
        hidden_variables,
    )
}

fn append_side_condition_shapes(
    prepared: &PreparedExpression,
    assumptions: &mut Vec<Expr<()>>,
    hidden_variables: &mut BTreeSet<Variable>,
) {
    for condition in &prepared.side_conditions {
        hidden_variables.insert(condition.introduced_variable.clone());
        assumptions.push(Expr::new(RawExpr::Binop(
            Binop::ElementOf,
            Expr::new(RawExpr::Variable(condition.introduced_variable.clone())),
            Expr::new(RawExpr::Type(condition.introduced_type.clone())),
        )));
        assumptions.extend(
            condition
                .defining_assertions
                .iter()
                .map(Expr::with_default_metadata),
        );
    }
}

fn extract_environment_iterator_with_hidden(
    assumptions: Vec<Expr<()>>,
    contextual_expressions: Vec<Expr<()>>,
    max_dimension: u64,
    hidden_variables: BTreeSet<Variable>,
) -> Result<EnvironmentIterator, ShapeError> {
    let mut specification = collect_environment_specification(&assumptions)?;
    let mut hidden_dimension_variables = BTreeSet::new();
    for hidden in &hidden_variables {
        if let Some(types) = specification.explicit_types.get(hidden) {
            for ty in types {
                collect_type_dimension_variables(ty, &mut hidden_dimension_variables);
            }
            for dimension in &hidden_dimension_variables {
                specification.variables.remove(dimension);
                specification.dimension_variables.remove(dimension);
            }
        }
    }
    let mut solver = Solver::new();
    let variable_types = infer_variable_types(&mut solver, specification)?;
    assert_positive_matrix_dimensions(&mut solver, &variable_types);
    let implicit_dimensions =
        collect_implicit_dimension_symbols(assumptions.iter().chain(contextual_expressions.iter()));
    for dimension in implicit_dimensions.values() {
        solver.assert(dimension.gt(0));
    }
    let (known_equalities, projections) = {
        let mut projections = BTreeMap::new();
        let mut context = ShapeContext {
            solver: &mut solver,
            variable_types: &variable_types,
            implicit_dimensions: &implicit_dimensions,
            projections: &mut projections,
            contextual: false,
            hidden_dimension_variables: &hidden_dimension_variables,
        };
        for assumption in &assumptions {
            context.constrain_assertion(assumption)?;
        }
        let known = context.known_equalities(&assumptions)?;
        check_base_constraints(context.solver)?;
        context.contextual = true;
        for expression in &contextual_expressions {
            if contains_implicit(expression) {
                context.constrain_assertion(expression)?;
            }
        }
        check_contextual_constraints(context.solver)?;
        (known, projections.into_iter().collect())
    };

    let dimensions: Vec<Int> = variable_types
        .iter()
        .filter(|(variable, _)| !hidden_variables.contains(*variable))
        .flat_map(|(_, shape)| shape_dimensions(shape))
        .chain(implicit_dimensions.values().cloned())
        .collect();
    let finished = !dimensions.is_empty() && max_dimension == 0;
    let dimension_count = u64::try_from(dimensions.len()).map_err(|_| {
        ShapeError::Unsupported("too many environment dimensions to enumerate".to_owned())
    })?;
    let max_dimension_sum = dimension_count.checked_mul(max_dimension).ok_or_else(|| {
        ShapeError::Unsupported("maximum environment dimension sum overflows u64".to_owned())
    })?;
    let mut iterator = EnvironmentIterator {
        solver,
        variable_types,
        implicit_dimensions: implicit_dimensions.into_iter().collect(),
        dimensions,
        known_equalities,
        projections,
        dimension_sum: dimension_count,
        max_dimension_sum,
        dimensionless_yielded: false,
        finished,
        hidden_variables,
    };
    if !iterator.dimensions.is_empty() && !iterator.finished {
        let max_dimension = Int::from_u64(max_dimension);
        for dimension in &iterator.dimensions {
            iterator.solver.assert(dimension.le(&max_dimension));
        }
        iterator.push_dimension_sum();
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

fn check_contextual_constraints(solver: &mut Solver) -> Result<(), ShapeError> {
    match solver.check() {
        SatResult::Sat => Ok(()),
        SatResult::Unsat => Err(ShapeError::InvalidTyping(
            "contextual implicit matrix dimensions are inconsistent".to_owned(),
        )),
        SatResult::Unknown => Err(ShapeError::Unknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown reason".to_owned()),
        )),
    }
}

impl EnvironmentIterator {
    fn push_dimension_sum(&mut self) {
        self.solver.push();
        self.solver
            .assert(Int::add(&self.dimensions).eq(Int::from_u64(self.dimension_sum)));
    }

    fn environment_from_model(&self, model: &z3::Model) -> Result<Environment, ShapeError> {
        let mut environment = Environment {
            equalities: self.known_equalities.clone(),
            ..Environment::default()
        };
        for (variable, shape) in &self.variable_types {
            if self.hidden_variables.contains(variable) {
                continue;
            }
            let ty = concrete_type(model, shape)?;
            environment.types.insert(variable.clone(), ty);
        }
        for (dimension, expression) in &self.implicit_dimensions {
            environment
                .implicit_dimensions
                .insert(*dimension, model_u64(model, expression)?);
        }
        for (expression, projection) in &self.projections {
            environment
                .equalities
                .insert(expression.clone(), model_u64(model, projection)?);
        }
        Ok(environment)
    }

    fn advance_dimension_sum(&mut self) {
        self.solver.pop(1);
        if self.dimension_sum == self.max_dimension_sum {
            self.finished = true;
        } else {
            self.dimension_sum = self.dimension_sum.checked_add(1).unwrap();
            self.push_dimension_sum();
        }
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
                    let blocker = self
                        .dimensions
                        .iter()
                        .chain(self.projections.iter().map(|(_, value)| value))
                        .map(|expression| {
                            let value = model
                                .eval(expression, false)
                                .expect("environment dimension must have a model value");
                            expression.eq(value).not()
                        })
                        .collect::<Vec<_>>();
                    self.solver.assert(Bool::or(&blocker));
                    return Some(Ok(environment));
                }
                SatResult::Unsat => {
                    self.advance_dimension_sum();
                    if self.finished {
                        return None;
                    }
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

fn collect_implicit_dimension_symbols<'a>(
    expressions: impl Iterator<Item = &'a Expr<()>>,
) -> BTreeMap<ImplicitDimension, Int> {
    let mut dimensions = BTreeSet::new();
    for expression in expressions {
        collect_implicit_dimensions(expression, &mut dimensions);
    }
    dimensions
        .into_iter()
        .map(|dimension| (dimension, Int::new_const(dimension.z3_name())))
        .collect()
}

fn contains_implicit(expression: &Expr<()>) -> bool {
    let mut dimensions = BTreeSet::new();
    collect_implicit_dimensions(expression, &mut dimensions);
    !dimensions.is_empty()
}

fn collect_implicit_dimensions(
    expression: &Expr<()>,
    dimensions: &mut BTreeSet<ImplicitDimension>,
) {
    match &expression.raw {
        RawExpr::IdentityMatrix { dimension } => {
            dimensions.insert(*dimension);
        }
        RawExpr::StandardBasis { index, dimension } => {
            dimensions.insert(*dimension);
            collect_implicit_dimensions(index, dimensions);
        }
        RawExpr::ZeroMatrix { rows, cols } => {
            dimensions.insert(*rows);
            dimensions.insert(*cols);
        }
        RawExpr::Type(ty) => collect_type_implicit_dimensions(ty, dimensions),
        RawExpr::Matrix(matrix) => {
            for element in &matrix.elements {
                collect_implicit_dimensions(element, dimensions);
            }
        }
        RawExpr::Monop(_, inner) => collect_implicit_dimensions(inner, dimensions),
        RawExpr::Binop(_, left, right) => {
            collect_implicit_dimensions(left, dimensions);
            collect_implicit_dimensions(right, dimensions);
        }
        RawExpr::Triop(_, first, second, third) => {
            collect_implicit_dimensions(first, dimensions);
            collect_implicit_dimensions(second, dimensions);
            collect_implicit_dimensions(third, dimensions);
        }
        RawExpr::Finop(_, expressions) => {
            for expression in expressions {
                collect_implicit_dimensions(expression, dimensions);
            }
        }
        RawExpr::CmpChain(chain) => {
            collect_implicit_dimensions(&chain.start, dimensions);
            for (_, expression) in &chain.assertions {
                collect_implicit_dimensions(expression, dimensions);
            }
        }
        RawExpr::LogicChain(chain) => {
            collect_implicit_dimensions(&chain.start, dimensions);
            for (_, expression) in &chain.assertions {
                collect_implicit_dimensions(expression, dimensions);
            }
        }
        RawExpr::Seqop(_, range, body) => {
            collect_implicit_dimensions(&range.from, dimensions);
            collect_implicit_dimensions(&range.to, dimensions);
            collect_implicit_dimensions(body, dimensions);
        }
        RawExpr::Hole | RawExpr::Variable(_) | RawExpr::NatLiteral(_) => {}
    }
}

fn collect_type_implicit_dimensions(
    ty: &TypeExpr<()>,
    dimensions: &mut BTreeSet<ImplicitDimension>,
) {
    match ty {
        TypeExpr::Matrix(rows, cols) | TypeExpr::Seq(rows, cols) => {
            collect_implicit_dimensions(rows, dimensions);
            collect_implicit_dimensions(cols, dimensions);
        }
        _ => {}
    }
}

struct ShapeContext<'a> {
    solver: &'a mut Solver,
    variable_types: &'a BTreeMap<Variable, Shape>,
    implicit_dimensions: &'a BTreeMap<ImplicitDimension, Int>,
    projections: &'a mut BTreeMap<Expr<()>, Int>,
    contextual: bool,
    hidden_dimension_variables: &'a BTreeSet<Variable>,
}

impl ShapeContext<'_> {
    fn implicit_dimension(&self, dimension: ImplicitDimension) -> Int {
        self.implicit_dimensions[&dimension].clone()
    }

    fn is_implicit_dimension(&self, dimension: &Int) -> bool {
        self.implicit_dimensions
            .values()
            .any(|implicit| implicit == dimension)
    }

    fn shape_depends_on_implicit(&self, shape: &Shape) -> bool {
        match shape {
            Shape::Matrix(rows, cols) => {
                self.is_implicit_dimension(rows) || self.is_implicit_dimension(cols)
            }
            Shape::Seq(element, length) => {
                self.is_implicit_dimension(length) || self.shape_depends_on_implicit(element)
            }
            _ => false,
        }
    }

    fn assert_if_relevant(&mut self, assertion: Bool, dimensions: &[&Int]) {
        if !self.contextual
            || dimensions
                .iter()
                .any(|dimension| self.is_implicit_dimension(dimension))
        {
            self.solver.assert(assertion);
        }
    }

    fn assert_dimensions_equal(&mut self, left: &Int, right: &Int) {
        self.assert_if_relevant(left.eq(right), &[left, right]);
    }

    fn assert_typing_failure(&mut self, shape: &Shape) {
        if !self.contextual || self.shape_depends_on_implicit(shape) {
            self.solver.assert(Bool::from_bool(false));
        }
    }

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
        if !self.contextual
            && let RawExpr::CmpChain(chain) = &expression.raw
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
            RawExpr::Variable(variable) if self.hidden_dimension_variables.contains(variable) => {
                // Symbolic dimensions of hidden generated values reuse internal
                // dimension names without becoming user environment variables.
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
            RawExpr::IdentityMatrix { dimension } => {
                let dimension = self.implicit_dimension(*dimension);
                Ok(Shape::Matrix(dimension.clone(), dimension))
            }
            RawExpr::StandardBasis { index, dimension } => {
                let dimension = self.implicit_dimension(*dimension);
                let index_value = self.lower_nat(index)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "standard basis index is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.projections.insert(index.clone(), index_value.clone());
                self.assert_if_relevant(index_value.ge(1), &[&dimension]);
                self.assert_if_relevant(index_value.le(&dimension), &[&dimension]);
                Ok(Shape::Matrix(dimension, Int::from_u64(1)))
            }
            RawExpr::ZeroMatrix { rows, cols } => Ok(Shape::Matrix(
                self.implicit_dimension(*rows),
                self.implicit_dimension(*cols),
            )),
            RawExpr::Variable(variable) => {
                self.variable_types.get(variable).cloned().ok_or_else(|| {
                    ShapeError::InvalidTyping(format!(
                        "missing inferred type for {}",
                        variable_z3_name(variable)
                    ))
                })
            }
            RawExpr::NatLiteral(_) => Ok(Shape::Nat),
            RawExpr::Matrix(matrix) => self.infer_block_matrix(matrix),
            RawExpr::Monop(op, inner) => {
                let shape = self.infer(inner)?;
                match (op, shape) {
                    (Monop::Transpose, Shape::Matrix(rows, cols)) => Ok(Shape::Matrix(cols, rows)),
                    (Monop::Inverse, Shape::Matrix(rows, cols)) => {
                        self.assert_dimensions_equal(&rows, &cols);
                        Ok(Shape::Matrix(rows, cols))
                    }
                    (Monop::Trace | Monop::Det, Shape::Matrix(rows, cols)) => {
                        self.assert_dimensions_equal(&rows, &cols);
                        Ok(Shape::Real)
                    }
                    (Monop::Trace | Monop::Det, shape) => {
                        self.assert_typing_failure(&shape);
                        Ok(Shape::Real)
                    }
                    (Monop::Norm2, _) => Err(ShapeError::Unsupported(
                        "2-norm must be lowered before shape inference".to_owned(),
                    )),
                    (Monop::Norm1 | Monop::NormInfty | Monop::NormFrob, _) => Ok(Shape::Real),
                    (_, shape) => Ok(shape),
                }
            }
            RawExpr::Binop(Binop::ElementOf, left, right) => self.constrain_membership(left, right),
            RawExpr::Binop(Binop::Cast, target, value) => self.infer_cast(target, value),
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
                    self.assert_dimensions_equal(rows, cols);
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
            RawExpr::Finop(Finop::And | Finop::Or, expressions) => {
                if expressions.is_empty() {
                    return Err(ShapeError::InvalidTyping(
                        "logical finite operations require at least one operand".to_owned(),
                    ));
                }
                for expression in expressions {
                    if !matches!(self.infer(expression)?, Shape::Bool) {
                        return Err(ShapeError::InvalidTyping(
                            "logical operations require Boolean operands".to_owned(),
                        ));
                    }
                }
                Ok(Shape::Bool)
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
                if !matches!(self.infer(&chain.start)?, Shape::Bool) {
                    return Err(ShapeError::InvalidTyping(
                        "logical operations require Boolean operands".to_owned(),
                    ));
                }
                for (_, expression) in &chain.assertions {
                    if !matches!(self.infer(expression)?, Shape::Bool) {
                        return Err(ShapeError::InvalidTyping(
                            "logical operations require Boolean operands".to_owned(),
                        ));
                    }
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
                self.assert_if_relevant(from.ge(1), &[&from]);
                self.assert_if_relevant(from.le(&to), &[&from, &to]);
                let lengths =
                    indexed_sequence_lengths(body, &range.index_variable, self.variable_types)?;
                if lengths.is_empty() {
                    return Err(ShapeError::InvalidTyping(
                        "sequence operation body does not index a sequence".to_owned(),
                    ));
                }
                for length in lengths {
                    self.assert_if_relevant(to.le(&length), &[&to, &length]);
                }
                if !self.contextual {
                    self.projections.insert(range.from.clone(), from);
                    self.projections.insert(range.to.clone(), to);
                }
                let shape = self.infer(body)?;
                if matches!(op, SeqOp::Prod)
                    && let Shape::Matrix(rows, cols) = &shape
                {
                    self.assert_dimensions_equal(rows, cols);
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
                self.assert_dimensions_equal(rows, &row_value);
                self.assert_dimensions_equal(cols, &col_value);
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
                self.assert_dimensions_equal(length, &length_value);
                self.constrain_shape_type(element, expected_element)?;
            }
            _ => self.assert_typing_failure(actual),
        }
        Ok(Shape::Bool)
    }

    fn infer_cast(&mut self, target: &Expr<()>, value: &Expr<()>) -> Result<Shape, ShapeError> {
        let RawExpr::Type(target) = &target.raw else {
            return Err(ShapeError::InvalidTyping(
                "cast target must be a type expression".to_owned(),
            ));
        };
        let value = self.infer(value)?;
        match (target, value) {
            (TypeExpr::Real, Shape::Real) => Ok(Shape::Real),
            (TypeExpr::Real, Shape::Matrix(rows, cols)) => {
                self.assert_dimensions_equal(&rows, &Int::from_u64(1));
                self.assert_dimensions_equal(&cols, &Int::from_u64(1));
                Ok(Shape::Real)
            }
            (TypeExpr::Matrix(rows, cols), Shape::Real) => {
                let rows_value = self.lower_nat(rows)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "cast matrix row dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                let cols_value = self.lower_nat(cols)?.ok_or_else(|| {
                    ShapeError::Unsupported(
                        "cast matrix column dimension is not linear natural arithmetic".to_owned(),
                    )
                })?;
                self.projections.insert(rows.clone(), rows_value.clone());
                self.projections.insert(cols.clone(), cols_value.clone());
                self.assert_dimensions_equal(&rows_value, &Int::from_u64(1));
                self.assert_dimensions_equal(&cols_value, &Int::from_u64(1));
                Ok(Shape::Matrix(rows_value, cols_value))
            }
            (TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Seq(_, _), _) => Err(
                ShapeError::Unsupported("only real and 1x1 matrix casts are supported".to_owned()),
            ),
            (TypeExpr::Real | TypeExpr::Matrix(_, _), _) => Err(ShapeError::InvalidTyping(
                "cast requires a real scalar or a 1x1 matrix operand".to_owned(),
            )),
        }
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
                self.assert_dimensions_equal(rows, &row_value);
                self.assert_dimensions_equal(cols, &col_value);
                Ok(())
            }
            (Shape::Seq(_, _), TypeExpr::Seq(_, _)) => Err(ShapeError::Unsupported(
                "nested sequence constraints are not supported".to_owned(),
            )),
            _ => {
                self.assert_typing_failure(actual);
                Ok(())
            }
        }
    }

    fn add_shapes(&mut self, left: Shape, right: Shape) -> Result<Shape, ShapeError> {
        match (&left, &right) {
            (Shape::Matrix(lr, lc), Shape::Matrix(rr, rc)) => {
                self.assert_dimensions_equal(lr, rr);
                self.assert_dimensions_equal(lc, rc);
                Ok(left)
            }
            (Shape::Matrix(_, _), _) | (_, Shape::Matrix(_, _)) => {
                self.assert_typing_failure(&left);
                self.assert_typing_failure(&right);
                Ok(left)
            }
            _ => scalar_shape_lub(left, right),
        }
    }

    fn multiply_shapes(&mut self, left: Shape, right: Shape) -> Result<Shape, ShapeError> {
        match (left, right) {
            (Shape::Matrix(rows, inner), Shape::Matrix(right_inner, cols)) => {
                self.assert_dimensions_equal(&inner, &right_inner);
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
                self.assert_dimensions_equal(lr, rr);
                self.assert_dimensions_equal(lc, rc);
            }
            (Shape::Matrix(rows, cols), scalar) | (scalar, Shape::Matrix(rows, cols)) => {
                if require_scalar(scalar).is_ok() {
                    self.assert_dimensions_equal(rows, &Int::from_u64(1));
                    self.assert_dimensions_equal(cols, &Int::from_u64(1));
                } else {
                    self.assert_typing_failure(left);
                    self.assert_typing_failure(right);
                }
            }
            _ => {}
        }
    }

    fn division_scalar(&mut self, shape: Shape) -> Shape {
        match shape {
            Shape::Matrix(rows, cols) => {
                self.assert_dimensions_equal(&rows, &Int::from_u64(1));
                self.assert_dimensions_equal(&cols, &Int::from_u64(1));
                Shape::Real
            }
            shape => shape,
        }
    }

    fn infer_block_matrix(&mut self, matrix: &Matrix<Expr<()>>) -> Result<Shape, ShapeError> {
        let expected_elements = matrix.rows.checked_mul(matrix.cols).ok_or_else(|| {
            ShapeError::Unsupported("matrix dimensions overflow usize".to_owned())
        })?;
        if matrix.elements.len() != expected_elements {
            return Err(ShapeError::InvalidTyping(
                "matrix element count does not match its dimensions".to_owned(),
            ));
        }
        if (matrix.rows == 0) != (matrix.cols == 0) {
            return Err(ShapeError::InvalidTyping(
                "matrix dimensions must both be zero or both be nonzero".to_owned(),
            ));
        }
        if matrix.rows == 0 {
            return Ok(Shape::Matrix(Int::from_u64(0), Int::from_u64(0)));
        }

        let dimensions = matrix
            .elements
            .iter()
            .map(|element| block_shape_dimensions(self.infer(element)?))
            .collect::<Result<Vec<_>, _>>()?;
        let mut row_heights = Vec::with_capacity(matrix.rows);
        for row in 0..matrix.rows {
            let height = dimensions[row * matrix.cols].0.clone();
            for column in 1..matrix.cols {
                self.assert_dimensions_equal(&height, &dimensions[row * matrix.cols + column].0);
            }
            row_heights.push(height);
        }
        let mut column_widths = Vec::with_capacity(matrix.cols);
        for column in 0..matrix.cols {
            let width = dimensions[column].1.clone();
            for row in 1..matrix.rows {
                self.assert_dimensions_equal(&width, &dimensions[row * matrix.cols + column].1);
            }
            column_widths.push(width);
        }
        Ok(Shape::Matrix(
            Int::add(&row_heights),
            Int::add(&column_widths),
        ))
    }
}

fn block_shape_dimensions(shape: Shape) -> Result<(Int, Int), ShapeError> {
    match shape {
        Shape::Nat | Shape::Int | Shape::Real => Ok((Int::from_u64(1), Int::from_u64(1))),
        Shape::Matrix(rows, cols) if rows.as_u64() == Some(0) && cols.as_u64() == Some(0) => Err(
            ShapeError::InvalidTyping("empty matrices cannot be used as blocks".to_owned()),
        ),
        Shape::Matrix(rows, cols) => Ok((rows, cols)),
        Shape::Bool | Shape::Seq(_, _) => Err(ShapeError::InvalidTyping(
            "block matrix cells must be numeric scalars or matrices".to_owned(),
        )),
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
        RawExpr::StandardBasis {
            index: basis_index, ..
        } => {
            collect_indexed_sequence_lengths(basis_index, index, variable_types, lengths)?;
        }
        RawExpr::IdentityMatrix { .. }
        | RawExpr::ZeroMatrix { .. }
        | RawExpr::Type(_)
        | RawExpr::Hole
        | RawExpr::Variable(_)
        | RawExpr::NatLiteral(_) => {}
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
        RawExpr::StandardBasis { index, .. } => collect_variables_bound(index, variables, bound),
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
        RawExpr::IdentityMatrix { .. }
        | RawExpr::ZeroMatrix { .. }
        | RawExpr::Hole
        | RawExpr::NatLiteral(_) => {}
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
        RawExpr::StandardBasis { index, .. } => collect_range_bound_variables(index, variables),
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
        RawExpr::IdentityMatrix { .. }
        | RawExpr::ZeroMatrix { .. }
        | RawExpr::Type(_)
        | RawExpr::Hole
        | RawExpr::Variable(_)
        | RawExpr::NatLiteral(_) => {}
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
    use std::collections::BTreeSet;

    use ratex_parser::parse;

    use super::{
        ShapeError, collect_implicit_dimensions, extract_environment_iterator,
        extract_environment_iterator_with_context, extract_prepared_environment_iterator,
        infer_symbolic_type_environment,
    };
    use crate::{
        Annotation, Expr, Matrix, RawExpr, SeqType, Type, Variable, from_tex,
        preprocessing::prepare_expression, visit_mut::VisitContext,
    };

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
    fn prepared_square_root_definition_infers_squareness() {
        let assumptions = vec![expression(r"A^{\frac{1}{2}} = A^{\frac{1}{2}}")];
        let types = infer_symbolic_type_environment(&assumptions).unwrap();
        let prepared = assumptions
            .iter()
            .map(|expression| {
                prepare_expression(
                    &types,
                    expression,
                    VisitContext {
                        logical_polarity: true,
                    },
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let environments = extract_prepared_environment_iterator(&prepared, &[], 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(environments.len(), 2);
        assert!(environments.iter().all(|environment| {
            matches!(environment.types[&Variable::new("A")], Type::Matrix(rows, cols) if rows == cols)
        }));
    }

    #[test]
    fn prepared_two_norm_forms_infer_a_column_matrix() {
        for assertion in [
            r"\left\lVert A \right\rVert_{2} = 0",
            r"\left\lVert A \right\rVert_{2}^{2} = 0",
        ] {
            let assumptions = vec![expression(assertion)];
            let types = infer_symbolic_type_environment(&assumptions).unwrap();
            let prepared = assumptions
                .iter()
                .map(|expression| {
                    prepare_expression(
                        &types,
                        expression,
                        VisitContext {
                            logical_polarity: true,
                        },
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let environments = extract_prepared_environment_iterator(&prepared, &[], 2)
                .unwrap()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(environments.len(), 2);
            assert!(environments.iter().all(|environment| {
                matches!(environment.types[&Variable::new("A")], Type::Matrix(_, 1))
            }));
        }
    }

    #[test]
    fn casts_constrain_symbolic_matrix_targets_to_one_by_one() {
        let environment = environments(&[
            r"x \in \mathbb{R}",
            r"A = \operatorname{cast}(\mathbb{R}^{m \times n}, x)",
        ])
        .next()
        .unwrap()
        .unwrap();
        assert_eq!(environment.types[&Variable::new("A")], Type::Matrix(1, 1));
        assert_eq!(environment.equalities[&expression("m")], 1);
        assert_eq!(environment.equalities[&expression("n")], 1);
    }

    #[test]
    fn casts_to_real_constrain_matrix_operands_to_one_by_one() {
        let environment = environments(&[
            r"A \in \mathbb{R}^{m \times n}",
            r"x \in \mathbb{R}",
            r"x = \operatorname{cast}(\mathbb{R}, A)",
        ])
        .next()
        .unwrap()
        .unwrap();
        assert_eq!(environment.types[&Variable::new("A")], Type::Matrix(1, 1));
        assert_eq!(environment.types[&Variable::new("x")], Type::Real);
        assert_eq!(environment.equalities[&expression("m")], 1);
        assert_eq!(environment.equalities[&expression("n")], 1);
    }

    #[test]
    fn casts_reject_unsupported_types() {
        assert!(matches!(
            extract_environment_iterator(
                [
                    expression(r"x \in \mathbb{R}"),
                    expression(r"\operatorname{cast}(\mathbb{N}, x)")
                ]
                .into_iter(),
                2,
            ),
            Err(ShapeError::Unsupported(_))
        ));
    }

    #[test]
    fn enumerates_by_increasing_total_dimension() {
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
    fn enumeration_extends_coordinatewise_dimension_order() {
        let shapes = extract_environment_iterator([expression("U = U")].into_iter(), 2)
            .unwrap()
            .map(|environment| {
                let environment = environment.unwrap();
                let Type::Matrix(rows, cols) = environment.types[&Variable::new("U")] else {
                    panic!("expected a matrix")
                };
                (rows, cols)
            })
            .collect::<Vec<_>>();

        for (left_index, left) in shapes.iter().enumerate() {
            for (right_index, right) in shapes.iter().enumerate() {
                if left.0 <= right.0 && left.1 <= right.1 && left != right {
                    assert!(left_index < right_index, "{left:?} must precede {right:?}");
                }
            }
        }
        let tall = shapes
            .iter()
            .position(|shape| *shape == (2, 1))
            .expect("missing 2 by 1 matrix environment");
        let square = shapes
            .iter()
            .position(|shape| *shape == (2, 2))
            .expect("missing 2 by 2 matrix environment");
        assert!(tall < square);
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
    fn contextual_constants_have_independent_dimensions() {
        let assumptions = [
            expression(r"A \in \mathbb{R}^{2 \times 2}"),
            expression(r"B \in \mathbb{R}^{3 \times 3}"),
            expression(r"C \in \mathbb{R}^{2 \times 3}"),
            expression(r"D \in \mathbb{R}^{3}"),
        ];
        let contexts = [
            expression("A = I"),
            expression("B = I"),
            expression(r"C + \mathbb{0} = C"),
            expression(r"D + \mathbb{0} = D"),
        ];
        let mut environments = extract_environment_iterator_with_context(
            assumptions.into_iter(),
            contexts.iter().cloned(),
            3,
        )
        .unwrap();
        let environment = environments.next().unwrap().unwrap();
        assert!(environments.next().is_none());

        let values = contexts
            .iter()
            .map(|expression| {
                let mut dimensions = std::collections::BTreeSet::new();
                collect_implicit_dimensions(expression, &mut dimensions);
                dimensions
                    .into_iter()
                    .map(|dimension| environment.implicit_dimensions[&dimension])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(values[0], vec![2]);
        assert_eq!(values[1], vec![3]);
        assert_eq!(
            values[2].iter().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([2, 3])
        );
        assert_eq!(
            values[3].iter().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([1, 3])
        );
    }

    #[test]
    fn contextual_identity_rejects_a_rectangular_matrix() {
        assert!(matches!(
            extract_environment_iterator_with_context(
                [expression(r"A \in \mathbb{R}^{2 \times 3}")].into_iter(),
                [expression("A = I")].into_iter(),
                3,
            ),
            Err(ShapeError::InvalidTyping(_))
        ));
        assert!(matches!(
            extract_environment_iterator(
                [
                    expression(r"A \in \mathbb{R}^{2 \times 3}"),
                    expression("A = I"),
                ]
                .into_iter(),
                3,
            ),
            Err(ShapeError::Unsat(_))
        ));
    }

    #[test]
    fn implicit_dimensions_are_enumerated_and_blocked() {
        let context = expression("I = I");
        let mut dimensions = BTreeSet::new();
        collect_implicit_dimensions(&context, &mut dimensions);
        let dimensions: Vec<_> = dimensions.into_iter().collect();
        let values: Vec<_> = extract_environment_iterator_with_context(
            std::iter::empty::<Expr<()>>(),
            [context].into_iter(),
            3,
        )
        .unwrap()
        .map(|environment| {
            let environment = environment.unwrap();
            dimensions
                .iter()
                .map(|dimension| environment.implicit_dimensions[dimension])
                .collect::<Vec<_>>()
        })
        .collect();
        assert_eq!(values, vec![vec![1, 1], vec![2, 2], vec![3, 3]]);
    }

    #[test]
    fn ordinary_context_does_not_constrain_environment_shapes() {
        let environments = extract_environment_iterator_with_context(
            [expression("A = A"), expression("B = B")].into_iter(),
            [expression("A B = A")].into_iter(),
            2,
        )
        .unwrap();
        assert!(environments.map(Result::unwrap).any(|environment| {
            let Type::Matrix(_, a_cols) = environment.types[&Variable::new("A")] else {
                panic!("expected matrix A")
            };
            let Type::Matrix(b_rows, _) = environment.types[&Variable::new("B")] else {
                panic!("expected matrix B")
            };
            a_cols != b_rows
        }));
    }

    #[test]
    fn standard_basis_index_is_checked_contextually() {
        let valid = extract_environment_iterator_with_context(
            [
                expression(r"v \in \mathbb{R}^{3}"),
                expression(r"i \in \mathbb{N}"),
                expression("i = 2"),
            ]
            .into_iter(),
            [expression("v = e_i")].into_iter(),
            3,
        )
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
        assert_eq!(valid.equalities[&expression("i")], 2);

        let symbolic_index = expression("e_{i+1}");
        let symbolic = extract_environment_iterator_with_context(
            [
                expression(r"v \in \mathbb{R}^{3}"),
                expression(r"i \in \mathbb{N}"),
                expression("i = 1"),
            ]
            .into_iter(),
            [Expr::new(RawExpr::CmpChain(crate::CmpChain {
                start: expression("v"),
                assertions: vec![(crate::Cmp::Eq, symbolic_index.clone())],
            }))]
            .into_iter(),
            3,
        )
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
        let RawExpr::StandardBasis { index, .. } = &symbolic_index.raw else {
            panic!("expected standard basis vector")
        };
        assert_eq!(symbolic.equalities[&index.with_default_metadata()], 2);

        assert!(matches!(
            extract_environment_iterator_with_context(
                [expression(r"v \in \mathbb{R}^{2}")].into_iter(),
                [expression("v = e_3")].into_iter(),
                3,
            ),
            Err(ShapeError::InvalidTyping(_))
        ));
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
    fn block_matrices_infer_totals_and_enforce_compatibility() {
        let valid = [
            r"A \in \mathbb{R}^{2 \times 2}",
            r"b \in \mathbb{R}^{2}",
            r"c \in \mathbb{R}^{2}",
            r"d \in \mathbb{R}",
            r"M = \begin{bmatrix}A & b \\ c^\top & d\end{bmatrix}",
        ];
        let environments = extract_environment_iterator(valid.into_iter().map(expression), 3)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(environments.len(), 1);
        assert_eq!(
            environments[0].types[&Variable::new("M")],
            Type::Matrix(3, 3)
        );

        for invalid in [
            [
                r"A \in \mathbb{R}^{2 \times 2}",
                r"b \in \mathbb{R}^{3}",
                r"M = \begin{bmatrix}A & b\end{bmatrix}",
            ],
            [
                r"A \in \mathbb{R}^{2 \times 2}",
                r"c \in \mathbb{R}^{3}",
                r"M = \begin{bmatrix}A \\ c^\top\end{bmatrix}",
            ],
        ] {
            assert!(matches!(
                extract_environment_iterator(invalid.into_iter().map(expression), 3),
                Err(ShapeError::Unsat(_))
            ));
        }
    }

    #[test]
    fn block_matrices_support_context_dependent_blocks() {
        let assumptions = [
            r"M \in \mathbb{R}^{2 \times 2}",
            r"M = \begin{bmatrix}I & \mathbb{0} \\ \mathbb{0} & I\end{bmatrix}",
        ];
        let environments = extract_environment_iterator(assumptions.into_iter().map(expression), 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(environments.len(), 1);
        assert!(
            environments[0]
                .implicit_dimensions
                .values()
                .all(|dimension| *dimension == 1)
        );
    }

    #[test]
    fn block_matrices_reject_unsupported_and_empty_blocks() {
        assert!(matches!(
            extract_environment_iterator(
                [
                    expression(r"b \in \mathbb{B}"),
                    expression(r"M = \begin{bmatrix}b\end{bmatrix}")
                ]
                .into_iter(),
                2,
            ),
            Err(ShapeError::InvalidTyping(_))
        ));

        let empty: Expr<()> = Expr::new(RawExpr::Matrix(Matrix {
            rows: 0,
            cols: 0,
            elements: Vec::new(),
        }));
        let matrix = Expr::new(RawExpr::Matrix(Matrix {
            rows: 1,
            cols: 1,
            elements: vec![empty],
        }));
        assert!(matches!(
            extract_environment_iterator([matrix].into_iter(), 2),
            Err(ShapeError::InvalidTyping(_))
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

    #[test]
    fn rejects_non_boolean_logical_operands() {
        assert!(matches!(
            extract_environment_iterator([expression(r"a \land b")].into_iter(), 2),
            Err(ShapeError::InvalidTyping(_))
        ));
    }

    #[test]
    fn trace_and_determinant_require_square_matrices() {
        for assertion in [r"\operatorname{tr}(A) = 0", r"\det(A) = 0"] {
            let environment = extract_environment_iterator([expression(assertion)].into_iter(), 2)
                .unwrap()
                .next()
                .unwrap()
                .unwrap();
            let Type::Matrix(rows, cols) = environment.types[&Variable::new("A")] else {
                panic!("expected a matrix")
            };
            assert_eq!(rows, cols);
        }

        for assumptions in [
            [r"a \in \mathbb{R}", r"\operatorname{tr}(a) = 0"],
            [r"a \in \mathbb{R}", r"\det(a) = 0"],
            [
                r"A \in \mathbb{R}^{1 \times 2}",
                r"\operatorname{tr}(A) = 0",
            ],
            [r"A \in \mathbb{R}^{1 \times 2}", r"\det(A) = 0"],
        ] {
            assert!(matches!(
                extract_environment_iterator(assumptions.into_iter().map(expression), 2,),
                Err(ShapeError::Unsat(_))
            ));
        }
    }
}
