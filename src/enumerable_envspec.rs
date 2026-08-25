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
    Binop, CmpChain, Environment, Expr, Finop, ImplicitDimension, Monop, NaturalEvaluationError,
    NaturalParameter, RawExpr, SeqOp, TypeExpr, Variable,
    preprocessing::PreparedExpression,
    preprocessing::prepare_expression,
    type_resolver::{
        MaybeTyped, SymbolicTypeEnvironment, TypeError, TypedMetadata, add_type, block_dimensions,
        multiply_type, require_numeric_scalar, scalar_lub,
    },
    visit::{self, Visit},
    visit_mut::VisitContext,
    z3_utils::{PresburgerClassification, classify_presburger, compare_int},
};

pub fn infer_symbolic_type_environment(
    assumptions: &[Expr<()>],
) -> Result<SymbolicTypeEnvironment, ShapeError> {
    let specification = collect_environment_specification(assumptions)?;
    let user_names = specification
        .variables
        .iter()
        .map(variable_z3_name)
        .collect::<BTreeSet<_>>();
    let mut generated_dimensions = BTreeSet::new();
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
            let ty = guessed_type_expr(&variable);
            collect_type_dimension_variables(&ty, &mut generated_dimensions);
            ty
        };
        types.insert(variable, ty);
    }
    if let Some(collision) = generated_dimensions
        .iter()
        .map(variable_z3_name)
        .find(|name| user_names.contains(name))
    {
        return Err(ShapeError::InvalidTyping(format!(
            "generated dimension variable collides with user variable {collision}"
        )));
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

fn type_error_to_shape_error(error: TypeError) -> ShapeError {
    match error {
        TypeError::Unsupported(message) => ShapeError::Unsupported(message.to_owned()),
        TypeError::Invalid(message) => ShapeError::InvalidTyping(message.to_owned()),
        TypeError::MissingType(variable) => ShapeError::InvalidTyping(format!(
            "missing inferred type for {}",
            variable_z3_name(&variable)
        )),
    }
}

type SymbolicTypes = BTreeMap<Variable, TypeExpr<()>>;
type NaturalSymbols = BTreeMap<NaturalParameter, Int>;

pub struct EnvironmentIterator {
    solver: Solver,
    parameters: Vec<(NaturalParameter, Int)>,
    parameter_values: Vec<Int>,
    dimension_sum: u64,
    max_dimension_sum: u64,
    dimensionless_yielded: bool,
    finished: bool,
    dimension_bound_is_exhaustive: bool,
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
    let assumptions: Vec<Expr<()>> = assumptions
        .map(|expression| expression.with_default_metadata())
        .collect();
    let contextual_expressions: Vec<Expr<()>> = contextual_expressions
        .map(|expression| expression.with_default_metadata())
        .collect();
    let types = infer_symbolic_type_environment(&assumptions)?;
    let positive = VisitContext {
        logical_polarity: true,
        active_ranges: Vec::new(),
    };
    let assumptions = assumptions
        .iter()
        .map(|expression| {
            prepare_expression(&types, expression, positive.clone())
                .map_err(type_error_to_shape_error)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let contextual_expressions = contextual_expressions
        .iter()
        .map(|expression| {
            prepare_expression(&types, expression, positive.clone())
                .map_err(type_error_to_shape_error)
        })
        .collect::<Result<Vec<_>, _>>()?;
    extract_prepared_environment_iterator(
        &types,
        &assumptions,
        &contextual_expressions,
        max_dimension,
    )
}

pub fn extract_prepared_environment_iterator(
    symbolic_types: &SymbolicTypeEnvironment,
    assumptions: &[PreparedExpression],
    contextual_expressions: &[PreparedExpression],
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    extract_prepared_environment_iterator_with_required_context(
        symbolic_types,
        assumptions,
        &[],
        contextual_expressions,
        max_dimension,
    )
}

pub(crate) fn extract_prepared_environment_iterator_with_required_context(
    symbolic_types: &SymbolicTypeEnvironment,
    assumptions: &[PreparedExpression],
    required_context: &[PreparedExpression],
    contextual_expressions: &[PreparedExpression],
    max_dimension: u64,
) -> Result<EnvironmentIterator, ShapeError> {
    let inputs =
        collect_prepared_dimension_inputs(assumptions, required_context, contextual_expressions)?;
    extract_typed_environment_iterator_with_hidden(
        symbolic_types,
        inputs.assumptions,
        inputs.required,
        inputs.contextual,
        max_dimension,
        inputs.hidden_types,
    )
}

pub(crate) struct DimensionEquivalenceQuery {
    solver: Solver,
    natural_symbols: NaturalSymbols,
}

impl DimensionEquivalenceQuery {
    pub(crate) fn necessarily_equal(
        &mut self,
        left: ImplicitDimension,
        right: ImplicitDimension,
    ) -> Option<bool> {
        if left == right {
            return Some(true);
        }
        let left = self
            .natural_symbols
            .get(&NaturalParameter::ImplicitDimension(left))?;
        let right = self
            .natural_symbols
            .get(&NaturalParameter::ImplicitDimension(right))?;
        self.solver.push();
        self.solver.assert(left.eq(right).not());
        let result = self.solver.check();
        self.solver.pop(1);
        match result {
            SatResult::Unsat => Some(true),
            SatResult::Sat => Some(false),
            SatResult::Unknown => None,
        }
    }
}

pub(crate) fn dimension_equivalence_query(
    symbolic_types: &SymbolicTypeEnvironment,
    assumptions: &[PreparedExpression],
    required_context: &[PreparedExpression],
) -> Result<DimensionEquivalenceQuery, ShapeError> {
    let inputs = collect_prepared_dimension_inputs(assumptions, required_context, &[])?;
    let system = build_dimension_constraint_system(
        symbolic_types,
        &inputs.assumptions,
        &inputs.required,
        &inputs.contextual,
        &inputs.hidden_types,
        None,
    )?;
    Ok(DimensionEquivalenceQuery {
        solver: system.solver,
        natural_symbols: system.natural_symbols,
    })
}

struct PreparedDimensionInputs {
    assumptions: Vec<Expr<TypedMetadata>>,
    required: Vec<Expr<TypedMetadata>>,
    contextual: Vec<Expr<TypedMetadata>>,
    hidden_types: BTreeMap<Variable, TypeExpr<()>>,
}

fn collect_prepared_dimension_inputs(
    assumptions: &[PreparedExpression],
    required_context: &[PreparedExpression],
    contextual_expressions: &[PreparedExpression],
) -> Result<PreparedDimensionInputs, ShapeError> {
    let mut hidden_types = BTreeMap::new();
    let mut prepared_assumptions: Vec<Expr<TypedMetadata>> = Vec::new();
    let mut prepared_required: Vec<Expr<TypedMetadata>> = Vec::new();
    let mut prepared_context: Vec<Expr<TypedMetadata>> = Vec::new();
    for prepared in assumptions {
        prepared_assumptions.push(prepared.expression.clone());
        append_side_condition_definitions(prepared, &mut prepared_assumptions, &mut hidden_types)?;
    }
    for prepared in required_context {
        prepared_required.push(prepared.expression.clone());
        append_side_condition_definitions(prepared, &mut prepared_assumptions, &mut hidden_types)?;
    }
    for prepared in contextual_expressions {
        prepared_context.push(prepared.expression.clone());
        // Generated definitions are typing obligations and must not be skipped by
        // the ordinary-context implicit-nonce filter.
        append_side_condition_definitions(prepared, &mut prepared_assumptions, &mut hidden_types)?;
    }
    Ok(PreparedDimensionInputs {
        assumptions: prepared_assumptions,
        required: prepared_required,
        contextual: prepared_context,
        hidden_types,
    })
}

fn append_side_condition_definitions(
    prepared: &PreparedExpression,
    assumptions: &mut Vec<Expr<TypedMetadata>>,
    hidden_types: &mut BTreeMap<Variable, TypeExpr<()>>,
) -> Result<(), ShapeError> {
    for condition in &prepared.side_conditions {
        if let Some(previous) = hidden_types.insert(
            condition.introduced_variable.clone(),
            condition.introduced_type.clone(),
        ) && previous != condition.introduced_type
        {
            return Err(ShapeError::InvalidTyping(format!(
                "generated variable {} has incompatible inferred types",
                condition.introduced_variable.z3_name()
            )));
        }
        assumptions.extend(condition.defining_assertions.iter().cloned());
    }
    Ok(())
}

fn extract_typed_environment_iterator_with_hidden<Metadata: MaybeTyped>(
    symbolic_types: &SymbolicTypeEnvironment,
    assumptions: Vec<Expr<Metadata>>,
    required_context: Vec<Expr<Metadata>>,
    contextual_expressions: Vec<Expr<Metadata>>,
    max_dimension: u64,
    hidden_types: BTreeMap<Variable, TypeExpr<()>>,
) -> Result<EnvironmentIterator, ShapeError> {
    let DimensionConstraintSystem {
        mut solver,
        variable_types,
        natural_symbols,
        dependent_dimension_cases,
    } = build_dimension_constraint_system(
        symbolic_types,
        &assumptions,
        &required_context,
        &contextual_expressions,
        &hidden_types,
        Some(max_dimension),
    )?;

    let structural_dimensions = lower_structural_dimensions(&variable_types, &natural_symbols)?;
    let parameters = natural_symbols.into_iter().collect::<Vec<_>>();
    let parameter_values = parameters
        .iter()
        .map(|(_, value)| value.clone())
        .collect::<Vec<_>>();
    let mut exhaustiveness_values = parameter_values.clone();
    exhaustiveness_values.extend(structural_dimensions.iter().cloned());
    let dimension_bound_is_exhaustive = dimension_bound_is_exhaustive(
        &mut solver,
        &exhaustiveness_values,
        &dependent_dimension_cases,
        max_dimension,
    );
    let max_dimension_value = Int::from_u64(max_dimension);
    for value in &parameter_values {
        solver.assert(value.le(&max_dimension_value));
    }
    for dimension in &structural_dimensions {
        solver.assert(dimension.le(&max_dimension_value));
    }
    for (guard, dimension) in &dependent_dimension_cases {
        solver.assert(guard.implies(dimension.le(&max_dimension_value)));
    }
    let finished = false;
    let parameter_count = u64::try_from(parameter_values.len()).map_err(|_| {
        ShapeError::Unsupported("too many natural parameters to enumerate".to_owned())
    })?;
    let max_dimension_sum = parameter_count.checked_mul(max_dimension).ok_or_else(|| {
        ShapeError::Unsupported("maximum natural-parameter sum overflows u64".to_owned())
    })?;
    let mut iterator = EnvironmentIterator {
        solver,
        parameters,
        parameter_values,
        dimension_sum: 0,
        max_dimension_sum,
        dimensionless_yielded: false,
        finished,
        dimension_bound_is_exhaustive,
    };
    if !iterator.parameter_values.is_empty() && !iterator.finished {
        iterator.push_dimension_sum();
    }
    Ok(iterator)
}

struct DimensionConstraintSystem {
    solver: Solver,
    variable_types: SymbolicTypes,
    natural_symbols: NaturalSymbols,
    dependent_dimension_cases: Vec<(Bool, Int)>,
}

fn build_dimension_constraint_system<Metadata: MaybeTyped>(
    symbolic_types: &SymbolicTypeEnvironment,
    assumptions: &[Expr<Metadata>],
    required_context: &[Expr<Metadata>],
    contextual_expressions: &[Expr<Metadata>],
    hidden_types: &BTreeMap<Variable, TypeExpr<()>>,
    max_dimension: Option<u64>,
) -> Result<DimensionConstraintSystem, ShapeError> {
    let hidden_variables = hidden_types.keys().cloned().collect::<BTreeSet<_>>();
    if let Some(collision) = hidden_variables
        .iter()
        .find(|variable| symbolic_types.types.contains_key(*variable))
    {
        return Err(ShapeError::InvalidTyping(format!(
            "generated variable {} collides with a user variable",
            collision.z3_name()
        )));
    }
    let mut solver = Solver::new();
    let implicit_dimensions = collect_implicit_dimension_ids(
        assumptions
            .iter()
            .chain(required_context.iter())
            .chain(contextual_expressions.iter()),
    );
    let (variable_types, natural_symbols) = collect_symbolic_types_and_natural_symbols(
        &mut solver,
        symbolic_types,
        hidden_types,
        &implicit_dimensions,
    )?;
    assert_positive_structural_dimensions(&mut solver, &variable_types, &natural_symbols)?;
    let dependent_dimension_cases =
        dependent_structural_dimension_cases(&variable_types, &natural_symbols, max_dimension)?;
    for (guard, dimension) in &dependent_dimension_cases {
        solver.assert(guard.implies(dimension.gt(0)));
    }
    {
        let mut context = DimensionConstraintBuilder {
            solver: &mut solver,
            variable_types: &variable_types,
            natural_symbols: &natural_symbols,
            mode: ConstraintMode::Permanent,
            locals: Vec::new(),
            guards: Vec::new(),
            max_dimension,
        };
        for assumption in assumptions {
            context.constrain_top_level_assertion(assumption)?;
        }
        run_dimension_constraint_visitors(&mut context, assumptions)?;
        run_dimension_constraint_visitors(&mut context, required_context)?;
        check_base_constraints(context.solver)?;
        context.mode = ConstraintMode::Contextual;
        run_dimension_constraint_visitors(&mut context, contextual_expressions)?;
        check_contextual_constraints(context.solver)?;
    }

    Ok(DimensionConstraintSystem {
        solver,
        variable_types,
        natural_symbols,
        dependent_dimension_cases,
    })
}

fn dimension_bound_is_exhaustive(
    solver: &mut Solver,
    dimensions: &[Int],
    dependent_dimensions: &[(Bool, Int)],
    max_dimension: u64,
) -> bool {
    if dimensions.is_empty() && dependent_dimensions.is_empty() {
        return true;
    }

    let max_dimension = Int::from_u64(max_dimension);
    let mut exceeds_bound = dimensions
        .iter()
        .map(|dimension| dimension.gt(&max_dimension))
        .collect::<Vec<_>>();
    exceeds_bound.extend(
        dependent_dimensions
            .iter()
            .map(|(guard, dimension)| Bool::and(&[guard.clone(), dimension.gt(&max_dimension)])),
    );
    solver.push();
    solver.assert(Bool::or(&exceeds_bound));
    let result = solver.check();
    solver.pop(1);
    matches!(result, SatResult::Unsat)
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
        collect_variables(assumption, &mut specification.variables)?;
        collect_natural_position_variables(assumption, &mut specification.dimension_variables);
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
        let ty = ty.clone();
        collect_type_dimension_variables(&ty, &mut specification.dimension_variables);
        specification
            .explicit_types
            .entry(variable.clone())
            .or_default()
            .push(ty);
    }
    Ok(specification)
}

fn collect_symbolic_types_and_natural_symbols(
    solver: &mut Solver,
    symbolic_types: &SymbolicTypeEnvironment,
    hidden_types: &BTreeMap<Variable, TypeExpr<()>>,
    implicit_dimensions: &BTreeSet<ImplicitDimension>,
) -> Result<(SymbolicTypes, NaturalSymbols), ShapeError> {
    let mut all_types = symbolic_types
        .types
        .iter()
        .map(|(variable, ty)| (variable.clone(), ty.clone()))
        .collect::<BTreeMap<_, _>>();
    all_types.extend(hidden_types.clone());
    let mut implicit_dimensions = implicit_dimensions.clone();
    for ty in all_types.values() {
        collect_type_implicit_dimensions(ty, &mut implicit_dimensions);
    }
    let mut natural_variables = BTreeSet::new();
    for (variable, ty) in &all_types {
        if matches!(ty, TypeExpr::Nat) {
            natural_variables.insert(variable.clone());
        }
        collect_type_dimension_variables(ty, &mut natural_variables);
    }

    let mut natural_symbols = implicit_dimensions
        .iter()
        .map(|dimension| {
            let parameter = NaturalParameter::ImplicitDimension(*dimension);
            let symbol = Int::new_const(parameter.z3_name());
            solver.assert(symbol.gt(0));
            (parameter, symbol)
        })
        .collect::<BTreeMap<_, _>>();
    for variable in natural_variables {
        if let Some(ty) = symbolic_types.types.get(&variable)
            && !matches!(ty, TypeExpr::Nat)
        {
            return Err(ShapeError::InvalidTyping(format!(
                "dimension variable {} is not natural-valued",
                variable_z3_name(&variable)
            )));
        }
        let parameter = NaturalParameter::Variable(variable.clone());
        let symbol = Int::new_const(parameter.z3_name());
        solver.assert(symbol.ge(0));
        assert!(natural_symbols.insert(parameter, symbol).is_none());
    }

    for (parameter, symbol) in &natural_symbols {
        assert_eq!(
            symbol,
            &Int::new_const(parameter.z3_name()),
            "natural lowering must reuse the environment-query symbol names"
        );
    }

    Ok((all_types, natural_symbols))
}

fn assert_positive_structural_dimensions(
    solver: &mut Solver,
    variable_types: &BTreeMap<Variable, TypeExpr<()>>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
) -> Result<(), ShapeError> {
    for ty in variable_types.values() {
        for dimension in structural_dimensions(ty)? {
            let dimension = lower_required_natural(
                dimension,
                natural_symbols,
                "structural dimension is not linear natural arithmetic",
            )?;
            solver.assert(dimension.gt(0));
        }
    }
    Ok(())
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
    pub fn dimension_bound_is_exhaustive(&self) -> bool {
        self.dimension_bound_is_exhaustive
    }

    fn push_dimension_sum(&mut self) {
        self.solver.push();
        self.solver
            .assert(Int::add(&self.parameter_values).eq(Int::from_u64(self.dimension_sum)));
    }

    fn environment_from_model(&self, model: &z3::Model) -> Result<Environment, ShapeError> {
        Ok(Environment {
            natural_assignment: self
                .parameters
                .iter()
                .map(|(parameter, expression)| {
                    Ok((parameter.clone(), model_u64(model, expression)?))
                })
                .collect::<Result<_, ShapeError>>()?,
        })
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
        if self.parameter_values.is_empty() {
            if self.dimensionless_yielded {
                self.finished = true;
                return None;
            }
            self.dimensionless_yielded = true;
            return match self.solver.check() {
                SatResult::Sat => Some(
                    self.environment_from_model(
                        &self
                            .solver
                            .get_model()
                            .expect("satisfiable solver must have a model"),
                    ),
                ),
                SatResult::Unsat => {
                    self.finished = true;
                    None
                }
                SatResult::Unknown => {
                    self.finished = true;
                    Some(Err(ShapeError::Unknown(
                        self.solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "unknown reason".to_owned()),
                    )))
                }
            };
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
                        .parameter_values
                        .iter()
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

fn collect_implicit_dimension_ids<'a, Metadata: 'a>(
    expressions: impl Iterator<Item = &'a Expr<Metadata>>,
) -> BTreeSet<ImplicitDimension> {
    let mut dimensions = BTreeSet::new();
    for expression in expressions {
        collect_implicit_dimensions(expression, &mut dimensions);
    }
    dimensions
}

fn collect_implicit_dimensions<Metadata>(
    expression: &Expr<Metadata>,
    dimensions: &mut BTreeSet<ImplicitDimension>,
) {
    struct Collector<'a>(&'a mut BTreeSet<ImplicitDimension>);
    impl<Metadata> Visit<Metadata> for Collector<'_> {
        fn visit_raw_expr_implicit_dimension(&mut self, dimension: &ImplicitDimension) {
            self.0.insert(*dimension);
        }
        fn visit_raw_expr_identity_matrix(&mut self, dimension: &ImplicitDimension) {
            self.0.insert(*dimension);
        }
        fn visit_raw_expr_standard_basis(
            &mut self,
            index: &Expr<Metadata>,
            dimension: &ImplicitDimension,
        ) {
            self.0.insert(*dimension);
            self.visit_expr(index);
        }
        fn visit_raw_expr_zero_matrix(
            &mut self,
            rows: &ImplicitDimension,
            cols: &ImplicitDimension,
        ) {
            self.0.insert(*rows);
            self.0.insert(*cols);
        }
    }
    Collector(dimensions).visit_expr(expression);
}

fn collect_type_implicit_dimensions(
    ty: &TypeExpr<()>,
    dimensions: &mut BTreeSet<ImplicitDimension>,
) {
    match ty {
        TypeExpr::Matrix(rows, cols) => {
            collect_implicit_dimensions(rows, dimensions);
            collect_implicit_dimensions(cols, dimensions);
        }
        TypeExpr::Seq(element, length) => {
            collect_implicit_dimensions(element, dimensions);
            collect_implicit_dimensions(length, dimensions);
        }
        TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
    }
}

fn depends_on_implicit_dimension<Metadata>(expression: &Expr<Metadata>) -> bool {
    let mut dimensions = BTreeSet::new();
    collect_implicit_dimensions(expression, &mut dimensions);
    !dimensions.is_empty()
}

fn type_depends_on_implicit(ty: &TypeExpr<()>) -> bool {
    let mut dimensions = BTreeSet::new();
    collect_type_implicit_dimensions(ty, &mut dimensions);
    !dimensions.is_empty()
}

fn natural(value: u64) -> Expr<()> {
    Expr::new(RawExpr::NatLiteral(value))
}

fn implicit_dimension(dimension: ImplicitDimension) -> Expr<()> {
    Expr::new(RawExpr::ImplicitDimension(dimension))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConstraintMode {
    Permanent,
    Contextual,
}

struct DimensionConstraintBuilder<'a> {
    solver: &'a mut Solver,
    variable_types: &'a BTreeMap<Variable, TypeExpr<()>>,
    natural_symbols: &'a BTreeMap<NaturalParameter, Int>,
    mode: ConstraintMode,
    locals: Vec<(Variable, u64)>,
    guards: Vec<Bool>,
    max_dimension: Option<u64>,
}

impl DimensionConstraintBuilder<'_> {
    fn assert_if_relevant(&mut self, assertion: Bool, depends_on_implicit: bool) {
        if matches!(self.mode, ConstraintMode::Permanent) || depends_on_implicit {
            let assertion = if self.guards.is_empty() {
                assertion
            } else {
                Bool::and(&self.guards).implies(assertion)
            };
            self.solver.assert(assertion);
        }
    }

    fn assert_dimensions_equal<LeftMetadata, RightMetadata>(
        &mut self,
        left: &Expr<LeftMetadata>,
        right: &Expr<RightMetadata>,
    ) -> Result<(), ShapeError> {
        let left_value = required_natural(
            self.lower_nat(left)?,
            "matrix dimension is not linear natural arithmetic",
        )?;
        let right_value = required_natural(
            self.lower_nat(right)?,
            "matrix dimension is not linear natural arithmetic",
        )?;
        self.assert_if_relevant(
            left_value.eq(right_value),
            depends_on_implicit_dimension(left) || depends_on_implicit_dimension(right),
        );
        Ok(())
    }

    fn assert_natural_comparison<LeftMetadata, RightMetadata>(
        &mut self,
        left: &Expr<LeftMetadata>,
        comparison: crate::Cmp,
        right: &Expr<RightMetadata>,
    ) -> Result<(), ShapeError> {
        let left_value = required_natural(
            self.lower_nat(left)?,
            "natural constraint is not linear natural arithmetic",
        )?;
        let right_value = required_natural(
            self.lower_nat(right)?,
            "natural constraint is not linear natural arithmetic",
        )?;
        self.assert_if_relevant(
            compare_int(&left_value, comparison, &right_value),
            depends_on_implicit_dimension(left) || depends_on_implicit_dimension(right),
        );
        Ok(())
    }

    fn assert_typing_failure(&mut self, types: &[&TypeExpr<()>]) {
        if matches!(self.mode, ConstraintMode::Permanent)
            || types.iter().any(|ty| type_depends_on_implicit(ty))
        {
            self.assert_if_relevant(Bool::from_bool(false), true);
        }
    }

    fn constrain_top_level_assertion<Metadata>(
        &mut self,
        expression: &Expr<Metadata>,
    ) -> Result<(), ShapeError> {
        if let RawExpr::CmpChain(chain) = &expression.raw
            && let Some(comparison) = self.natural_comparison(chain)?
        {
            self.solver.assert(comparison);
        }
        Ok(())
    }

    fn natural_comparison<Metadata>(
        &self,
        chain: &CmpChain<Metadata>,
    ) -> Result<Option<Bool>, ShapeError> {
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

    fn lower_nat<Metadata>(&self, expression: &Expr<Metadata>) -> Result<Option<Int>, ShapeError> {
        let mut symbols = self.natural_symbols.clone();
        for (variable, value) in &self.locals {
            symbols.insert(
                NaturalParameter::Variable(variable.clone()),
                Int::from_u64(*value),
            );
        }
        match classify_presburger(expression, &symbols) {
            PresburgerClassification::NotNatural => return Ok(None),
            PresburgerClassification::Unsupported(message) => {
                return Err(ShapeError::Unsupported(message.to_owned()));
            }
            PresburgerClassification::Valid => {}
        }
        match crate::z3_utils::lower_natural_scoped_with(
            expression,
            &mut |parameter| {
                if let NaturalParameter::Variable(variable) = parameter
                    && let Some((_, value)) = self
                        .locals
                        .iter()
                        .rev()
                        .find(|(found, _)| found == variable)
                {
                    return Ok(Int::from_u64(*value));
                }
                self.natural_symbols
                    .get(parameter)
                    .cloned()
                    .ok_or_else(|| NaturalEvaluationError::MissingAssignment(parameter.clone()))
            },
            &mut |depth| Err(NaturalEvaluationError::UnboundNatural(depth)),
        ) {
            Ok(value) => Ok(Some(value)),
            Err(NaturalEvaluationError::MissingAssignment(_)) => Ok(None),
            Err(error) => Err(ShapeError::Unsupported(error.to_string())),
        }
    }

    fn type_of<Metadata: MaybeTyped>(
        &self,
        expression: &Expr<Metadata>,
    ) -> Result<TypeExpr<()>, ShapeError> {
        expression
            .meta
            .get_type()
            .map_err(type_error_to_shape_error)
    }

    fn constrain_types<Metadata>(
        &mut self,
        actual: &TypeExpr<()>,
        expected: &TypeExpr<Metadata>,
    ) -> Result<(), ShapeError> {
        let expected = expected.with_default_metadata();
        match (actual, &expected) {
            (TypeExpr::Bool, TypeExpr::Bool)
            | (TypeExpr::Nat, TypeExpr::Nat)
            | (TypeExpr::Int, TypeExpr::Int)
            | (TypeExpr::Real, TypeExpr::Real) => Ok(()),
            (TypeExpr::Matrix(rows, cols), TypeExpr::Matrix(expected_rows, expected_cols)) => {
                self.assert_dimensions_equal(rows, expected_rows)?;
                self.assert_dimensions_equal(cols, expected_cols)?;
                Ok(())
            }
            (TypeExpr::Seq(element, length), TypeExpr::Seq(expected_element, expected_length)) => {
                let RawExpr::Type(element) = &element.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "sequence element must be a type expression".to_owned(),
                    ));
                };
                let RawExpr::Type(expected_element) = &expected_element.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "sequence element must be a type expression".to_owned(),
                    ));
                };
                if matches!(expected_element, TypeExpr::Seq(_, _)) {
                    return Err(ShapeError::Unsupported(
                        "nested sequence constraints are not supported".to_owned(),
                    ));
                }
                self.assert_dimensions_equal(length, expected_length)?;
                self.constrain_types(element, expected_element)
            }
            _ => {
                self.assert_typing_failure(&[actual, &expected]);
                Ok(())
            }
        }
    }

    fn add_types(
        &mut self,
        left: TypeExpr<()>,
        right: TypeExpr<()>,
    ) -> Result<TypeExpr<()>, ShapeError> {
        match (&left, &right) {
            (TypeExpr::Matrix(lr, lc), TypeExpr::Matrix(rr, rc)) => {
                self.assert_dimensions_equal(lr, rr)?;
                self.assert_dimensions_equal(lc, rc)?;
                add_type(left, right).map_err(type_error_to_shape_error)
            }
            (TypeExpr::Matrix(_, _), _) | (_, TypeExpr::Matrix(_, _)) => {
                self.assert_typing_failure(&[&left, &right]);
                Ok(left)
            }
            _ => scalar_lub(left, right).map_err(type_error_to_shape_error),
        }
    }

    fn multiply_types(
        &mut self,
        left: TypeExpr<()>,
        right: TypeExpr<()>,
    ) -> Result<TypeExpr<()>, ShapeError> {
        match (&left, &right) {
            (TypeExpr::Matrix(_, inner), TypeExpr::Matrix(right_inner, _)) => {
                self.assert_dimensions_equal(inner, right_inner)?;
                multiply_type(left, right).map_err(type_error_to_shape_error)
            }
            (TypeExpr::Matrix(_, _), scalar) | (scalar, TypeExpr::Matrix(_, _)) => {
                require_numeric_scalar(scalar.clone()).map_err(type_error_to_shape_error)?;
                multiply_type(left, right).map_err(type_error_to_shape_error)
            }
            _ => scalar_lub(left, right).map_err(type_error_to_shape_error),
        }
    }

    fn equal_types(&mut self, left: &TypeExpr<()>, right: &TypeExpr<()>) -> Result<(), ShapeError> {
        match (left, right) {
            (TypeExpr::Matrix(lr, lc), TypeExpr::Matrix(rr, rc)) => {
                self.assert_dimensions_equal(lr, rr)?;
                self.assert_dimensions_equal(lc, rc)?;
            }
            (TypeExpr::Matrix(rows, cols), scalar) | (scalar, TypeExpr::Matrix(rows, cols)) => {
                if require_numeric_scalar(scalar.clone()).is_ok() {
                    self.assert_dimensions_equal(rows, &natural(1))?;
                    self.assert_dimensions_equal(cols, &natural(1))?;
                } else {
                    self.assert_typing_failure(&[left, right]);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

struct OperatorCompatibilityVisitor<'a, 'builder> {
    builder: &'a mut DimensionConstraintBuilder<'builder>,
    error: Option<ShapeError>,
}

impl OperatorCompatibilityVisitor<'_, '_> {
    fn constrain<Metadata: MaybeTyped>(
        &mut self,
        expression: &Expr<Metadata>,
    ) -> Result<(), ShapeError> {
        match &expression.raw {
            RawExpr::StandardBasis { index, dimension } => {
                let dimension = implicit_dimension(*dimension);
                self.builder
                    .assert_natural_comparison(index, crate::Cmp::Ge, &natural(1))?;
                self.builder
                    .assert_natural_comparison(index, crate::Cmp::Le, &dimension)?;
            }
            RawExpr::Monop(op, inner) => {
                let ty = self.builder.type_of(inner)?;
                match (op, &ty) {
                    (Monop::Inverse | Monop::Trace | Monop::Det, TypeExpr::Matrix(rows, cols)) => {
                        self.builder.assert_dimensions_equal(rows, cols)?;
                    }
                    (Monop::Trace | Monop::Det | Monop::Inverse, _) => {
                        self.builder.assert_typing_failure(&[&ty]);
                    }
                    (Monop::Norm2, _) => {
                        return Err(ShapeError::Unsupported(
                            "2-norm must be lowered before dimension inference".to_owned(),
                        ));
                    }
                    (Monop::Diag, _) => {}
                    (
                        Monop::Neg
                        | Monop::Transpose
                        | Monop::Norm1
                        | Monop::NormInfty
                        | Monop::NormFrob,
                        _,
                    ) => {}
                }
            }
            RawExpr::Binop(Binop::ElementOf, left, right) => {
                let RawExpr::Variable(variable) = &left.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "type membership requires a variable subject".to_owned(),
                    ));
                };
                let RawExpr::Type(expected) = &right.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "type membership requires a type expression".to_owned(),
                    ));
                };
                let actual = self
                    .builder
                    .variable_types
                    .get(variable)
                    .cloned()
                    .ok_or_else(|| {
                        ShapeError::InvalidTyping(
                            "membership subject has no inferred type".to_owned(),
                        )
                    })?;
                self.builder.constrain_types(&actual, expected)?;
            }
            RawExpr::Binop(Binop::Cast, target, value) => {
                let RawExpr::Type(target) = &target.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "cast target must be a type expression".to_owned(),
                    ));
                };
                let value = self.builder.type_of(value)?;
                match (target, &value) {
                    (TypeExpr::Real, TypeExpr::Real) => {}
                    (TypeExpr::Real, TypeExpr::Matrix(rows, cols)) => {
                        self.builder.assert_dimensions_equal(rows, &natural(1))?;
                        self.builder.assert_dimensions_equal(cols, &natural(1))?;
                    }
                    (TypeExpr::Matrix(rows, cols), TypeExpr::Real) => {
                        self.builder.assert_dimensions_equal(rows, &natural(1))?;
                        self.builder.assert_dimensions_equal(cols, &natural(1))?;
                    }
                    (TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Seq(_, _), _) => {
                        return Err(ShapeError::Unsupported(
                            "only real and 1x1 matrix casts are supported".to_owned(),
                        ));
                    }
                    (TypeExpr::Real | TypeExpr::Matrix(_, _), _) => {
                        self.builder.assert_typing_failure(&[&value])
                    }
                }
            }
            RawExpr::Binop(Binop::SingleSubscript, sequence, index) => {
                if !matches!(self.builder.type_of(sequence)?, TypeExpr::Seq(_, _)) {
                    return Err(ShapeError::InvalidTyping(
                        "subscripted expression is not a sequence".to_owned(),
                    ));
                }
                if !matches!(self.builder.type_of(index)?, TypeExpr::Nat) {
                    return Err(ShapeError::InvalidTyping(
                        "sequence index must be natural-number arithmetic".to_owned(),
                    ));
                }
            }
            RawExpr::Binop(Binop::Power, base, _) => {
                if let TypeExpr::Matrix(rows, cols) = self.builder.type_of(base)? {
                    self.builder.assert_dimensions_equal(&rows, &cols)?;
                }
            }
            RawExpr::Binop(Binop::Div, left, right) => {
                for operand in [left, right] {
                    if let TypeExpr::Matrix(rows, cols) = self.builder.type_of(operand)? {
                        self.builder.assert_dimensions_equal(&rows, &natural(1))?;
                        self.builder.assert_dimensions_equal(&cols, &natural(1))?;
                    }
                }
            }
            RawExpr::Binop(Binop::InnerProd, _, _) => {}
            RawExpr::Finop(Finop::Plus, expressions) => {
                let (first, rest) = expressions
                    .split_first()
                    .ok_or_else(|| ShapeError::InvalidTyping("empty addition".to_owned()))?;
                let mut ty = self.builder.type_of(first)?;
                for expression in rest {
                    ty = self
                        .builder
                        .add_types(ty, self.builder.type_of(expression)?)?;
                }
            }
            RawExpr::Finop(Finop::Times, expressions) => {
                let (first, rest) = expressions
                    .split_first()
                    .ok_or_else(|| ShapeError::InvalidTyping("empty multiplication".to_owned()))?;
                let mut ty = self.builder.type_of(first)?;
                for expression in rest {
                    ty = self
                        .builder
                        .multiply_types(ty, self.builder.type_of(expression)?)?;
                }
            }
            RawExpr::Finop(Finop::And | Finop::Or, expressions) => {
                if expressions.is_empty() {
                    return Err(ShapeError::InvalidTyping(
                        "logical finite operations require at least one operand".to_owned(),
                    ));
                }
                for operand in expressions {
                    if !matches!(self.builder.type_of(operand)?, TypeExpr::Bool) {
                        return Err(ShapeError::InvalidTyping(
                            "logical operations require Boolean operands".to_owned(),
                        ));
                    }
                }
            }
            RawExpr::Finop(Finop::Forall | Finop::Exists, _) => {
                return Err(ShapeError::Unsupported(
                    "quantified expressions are retained rather than dimensionally lowered"
                        .to_owned(),
                ));
            }
            RawExpr::Finop(Finop::Max | Finop::Min, _) | RawExpr::Triop(_, _, _, _) => {
                return Err(ShapeError::Unsupported(
                    "expression has unsupported dimension semantics".to_owned(),
                ));
            }
            RawExpr::CmpChain(chain) => {
                let mut previous = self.builder.type_of(&chain.start)?;
                for (_, current) in &chain.assertions {
                    let current = self.builder.type_of(current)?;
                    self.builder.equal_types(&previous, &current)?;
                    previous = current;
                }
            }
            RawExpr::LogicChain(chain) => {
                if !matches!(self.builder.type_of(&chain.start)?, TypeExpr::Bool) {
                    return Err(ShapeError::InvalidTyping(
                        "logical operations require Boolean operands".to_owned(),
                    ));
                }
                for (_, operand) in &chain.assertions {
                    if !matches!(self.builder.type_of(operand)?, TypeExpr::Bool) {
                        return Err(ShapeError::InvalidTyping(
                            "logical operations require Boolean operands".to_owned(),
                        ));
                    }
                }
            }
            RawExpr::Hole
            | RawExpr::ImplicitDimension(_)
            | RawExpr::BoundNatural(_)
            | RawExpr::IdentityMatrix { .. }
            | RawExpr::ZeroMatrix { .. }
            | RawExpr::Type(_)
            | RawExpr::Variable(_)
            | RawExpr::NatLiteral(_)
            | RawExpr::Matrix(_)
            | RawExpr::Seqop(_, _, _) => {}
        }
        Ok(())
    }
}

impl<Metadata: MaybeTyped> Visit<Metadata> for OperatorCompatibilityVisitor<'_, '_> {
    fn visit_expr(&mut self, node: &Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit::visit_expr(self, node);
        if node.meta.get_type().is_ok()
            && let Err(error) = self.constrain(node)
        {
            self.error = Some(error);
        }
    }

    fn visit_raw_expr_seqop(
        &mut self,
        _op: &SeqOp,
        range: &crate::Range<Metadata>,
        _body: &Expr<Metadata>,
    ) {
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
    }
}

struct BlockMatrixCompatibilityVisitor<'a, 'builder> {
    builder: &'a mut DimensionConstraintBuilder<'builder>,
    error: Option<ShapeError>,
}

impl<Metadata: MaybeTyped> Visit<Metadata> for BlockMatrixCompatibilityVisitor<'_, '_> {
    fn visit_expr(&mut self, node: &Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit::visit_expr(self, node);
        let RawExpr::Matrix(matrix) = &node.raw else {
            return;
        };
        let result = (|| {
            let expected = matrix.rows.checked_mul(matrix.cols).ok_or_else(|| {
                ShapeError::Unsupported("matrix dimensions overflow usize".to_owned())
            })?;
            if matrix.elements.len() != expected {
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
                return Ok(());
            }
            let dimensions = matrix
                .elements
                .iter()
                .map(|element| {
                    block_dimensions(self.builder.type_of(element)?)
                        .map_err(type_error_to_shape_error)
                })
                .collect::<Result<Vec<_>, _>>()?;
            for row in 0..matrix.rows {
                let height = &dimensions[row * matrix.cols].0;
                for column in 1..matrix.cols {
                    self.builder.assert_dimensions_equal(
                        height,
                        &dimensions[row * matrix.cols + column].0,
                    )?;
                }
            }
            for column in 0..matrix.cols {
                let width = &dimensions[column].1;
                for row in 1..matrix.rows {
                    self.builder.assert_dimensions_equal(
                        width,
                        &dimensions[row * matrix.cols + column].1,
                    )?;
                }
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.error = Some(error);
        }
    }

    fn visit_raw_expr_seqop(
        &mut self,
        _op: &SeqOp,
        range: &crate::Range<Metadata>,
        _body: &Expr<Metadata>,
    ) {
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
    }
}

struct SequenceCompatibilityVisitor<'a, 'builder> {
    builder: &'a mut DimensionConstraintBuilder<'builder>,
    error: Option<ShapeError>,
}

impl<Metadata: MaybeTyped> Visit<Metadata> for SequenceCompatibilityVisitor<'_, '_> {
    fn visit_expr(&mut self, node: &Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit::visit_expr(self, node);
        let RawExpr::Seqop(op, range, body) = &node.raw else {
            return;
        };
        let result = (|| {
            self.builder
                .assert_natural_comparison(&range.from, crate::Cmp::Le, &range.to)?;
            let lengths =
                indexed_sequence_lengths(body, &range.index_variable, self.builder.variable_types)?;
            if !lengths.is_empty() {
                self.builder
                    .assert_natural_comparison(&range.from, crate::Cmp::Ge, &natural(1))?;
            }
            for length in lengths {
                self.builder
                    .assert_natural_comparison(&range.to, crate::Cmp::Le, &length)?;
            }
            if matches!(op, SeqOp::Prod)
                && let TypeExpr::Matrix(rows, cols) = self.builder.type_of(body)?
            {
                self.builder.assert_dimensions_equal(&rows, &cols)?;
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.error = Some(error);
        }
    }

    fn visit_raw_expr_seqop(
        &mut self,
        _op: &SeqOp,
        range: &crate::Range<Metadata>,
        _body: &Expr<Metadata>,
    ) {
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
    }
}

struct SequenceBodyConstraintVisitor<'a, 'builder> {
    builder: &'a mut DimensionConstraintBuilder<'builder>,
    error: Option<ShapeError>,
}

impl<Metadata: MaybeTyped> Visit<Metadata> for SequenceBodyConstraintVisitor<'_, '_> {
    fn visit_raw_expr_seqop(
        &mut self,
        _op: &SeqOp,
        range: &crate::Range<Metadata>,
        body: &Expr<Metadata>,
    ) {
        if self.error.is_some() {
            return;
        }
        self.visit_expr(&range.from);
        self.visit_expr(&range.to);
        let Some(max_dimension) = self.builder.max_dimension else {
            return;
        };
        let result = (|| {
            let from = required_natural(
                self.builder.lower_nat(&range.from)?,
                "sequence lower bound is not linear natural arithmetic",
            )?;
            let to = required_natural(
                self.builder.lower_nat(&range.to)?,
                "sequence upper bound is not linear natural arithmetic",
            )?;
            for value in 0..=max_dimension {
                let value_ast = Int::from_u64(value);
                self.builder
                    .guards
                    .push(Bool::and(&[from.le(&value_ast), value_ast.le(&to)]));
                self.builder
                    .locals
                    .push((range.index_variable.clone(), value));
                let nested =
                    run_dimension_constraint_visitors(self.builder, std::slice::from_ref(body));
                self.builder.locals.pop();
                self.builder.guards.pop();
                nested?;
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.error = Some(error);
        }
    }
}

fn run_dimension_constraint_visitors<Metadata: MaybeTyped>(
    builder: &mut DimensionConstraintBuilder<'_>,
    expressions: &[Expr<Metadata>],
) -> Result<(), ShapeError> {
    for expression in expressions {
        let mut visitor = OperatorCompatibilityVisitor {
            builder,
            error: None,
        };
        visitor.visit_expr(expression);
        if let Some(error) = visitor.error {
            return Err(error);
        }
    }
    for expression in expressions {
        let mut visitor = BlockMatrixCompatibilityVisitor {
            builder,
            error: None,
        };
        visitor.visit_expr(expression);
        if let Some(error) = visitor.error {
            return Err(error);
        }
    }
    for expression in expressions {
        let mut visitor = SequenceCompatibilityVisitor {
            builder,
            error: None,
        };
        visitor.visit_expr(expression);
        if let Some(error) = visitor.error {
            return Err(error);
        }
    }
    for expression in expressions {
        let mut visitor = SequenceBodyConstraintVisitor {
            builder,
            error: None,
        };
        visitor.visit_expr(expression);
        if let Some(error) = visitor.error {
            return Err(error);
        }
    }
    Ok(())
}

fn lower_nat_via_to_z3<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
) -> Result<Option<Int>, ShapeError> {
    match classify_presburger(expression, natural_symbols) {
        PresburgerClassification::NotNatural => Ok(None),
        PresburgerClassification::Unsupported(message) => {
            Err(ShapeError::Unsupported(message.to_owned()))
        }
        PresburgerClassification::Valid => {
            crate::z3_utils::lower_natural_with(expression, &mut |parameter| {
                natural_symbols
                    .get(parameter)
                    .cloned()
                    .ok_or_else(|| NaturalEvaluationError::MissingAssignment(parameter.clone()))
            })
            .map(Some)
            .map_err(|error| ShapeError::Unsupported(error.to_string()))
        }
    }
}

fn required_natural(value: Option<Int>, message: &'static str) -> Result<Int, ShapeError> {
    value.ok_or_else(|| ShapeError::Unsupported(message.to_owned()))
}

fn lower_required_natural<Metadata>(
    expression: &Expr<Metadata>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
    message: &'static str,
) -> Result<Int, ShapeError> {
    required_natural(lower_nat_via_to_z3(expression, natural_symbols)?, message)
}

fn structural_dimensions(ty: &TypeExpr<()>) -> Result<Vec<&Expr<()>>, ShapeError> {
    match ty {
        TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => Ok(Vec::new()),
        TypeExpr::Matrix(rows, cols) => Ok([rows, cols]
            .into_iter()
            .filter(|dimension| !crate::type_expr::expression_contains_bound_natural(dimension))
            .collect()),
        TypeExpr::Seq(element, length) => {
            let RawExpr::Type(element) = &element.raw else {
                return Err(ShapeError::InvalidTyping(
                    "sequence element must be a type expression".to_owned(),
                ));
            };
            let mut dimensions = vec![length];
            dimensions.extend(structural_dimensions(element)?);
            Ok(dimensions)
        }
    }
}

fn dependent_structural_dimension_cases(
    variable_types: &BTreeMap<Variable, TypeExpr<()>>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
    max_dimension: Option<u64>,
) -> Result<Vec<(Bool, Int)>, ShapeError> {
    let Some(max_dimension) = max_dimension else {
        return Ok(Vec::new());
    };

    fn lower(
        expression: &Expr<()>,
        natural_symbols: &BTreeMap<NaturalParameter, Int>,
        bound_values: &[u64],
    ) -> Result<Int, ShapeError> {
        crate::z3_utils::lower_natural_scoped_with(
            expression,
            &mut |parameter| {
                natural_symbols
                    .get(parameter)
                    .cloned()
                    .ok_or_else(|| NaturalEvaluationError::MissingAssignment(parameter.clone()))
            },
            &mut |depth| {
                bound_values
                    .iter()
                    .rev()
                    .nth(depth)
                    .copied()
                    .map(Int::from_u64)
                    .ok_or(NaturalEvaluationError::UnboundNatural(depth))
            },
        )
        .map_err(|error| ShapeError::Unsupported(error.to_string()))
    }

    fn collect(
        ty: &TypeExpr<()>,
        natural_symbols: &BTreeMap<NaturalParameter, Int>,
        max_dimension: u64,
        bound_values: &mut Vec<u64>,
        guards: &mut Vec<Bool>,
        cases: &mut Vec<(Bool, Int)>,
    ) -> Result<(), ShapeError> {
        let guard = || {
            if guards.is_empty() {
                Bool::from_bool(true)
            } else {
                Bool::and(guards)
            }
        };
        match ty {
            TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
            TypeExpr::Matrix(rows, cols) => {
                for dimension in [rows, cols] {
                    if crate::type_expr::expression_contains_bound_natural(dimension) {
                        cases.push((guard(), lower(dimension, natural_symbols, bound_values)?));
                    }
                }
            }
            TypeExpr::Seq(element, length) => {
                if crate::type_expr::expression_contains_bound_natural(length) {
                    cases.push((guard(), lower(length, natural_symbols, bound_values)?));
                }
                let RawExpr::Type(element) = &element.raw else {
                    return Err(ShapeError::InvalidTyping(
                        "sequence element must be a type expression".to_owned(),
                    ));
                };
                let length = lower(length, natural_symbols, bound_values)?;
                for position in 1..=max_dimension {
                    let position_ast = Int::from_u64(position);
                    guards.push(position_ast.le(&length));
                    bound_values.push(position);
                    collect(
                        element,
                        natural_symbols,
                        max_dimension,
                        bound_values,
                        guards,
                        cases,
                    )?;
                    bound_values.pop();
                    guards.pop();
                }
            }
        }
        Ok(())
    }

    let mut cases = Vec::new();
    for ty in variable_types.values() {
        collect(
            ty,
            natural_symbols,
            max_dimension,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut cases,
        )?;
    }
    Ok(cases)
}

fn lower_structural_dimensions(
    variable_types: &BTreeMap<Variable, TypeExpr<()>>,
    natural_symbols: &BTreeMap<NaturalParameter, Int>,
) -> Result<Vec<Int>, ShapeError> {
    let mut lowered = Vec::new();
    for ty in variable_types.values() {
        for dimension in structural_dimensions(ty)? {
            lowered.push(lower_required_natural(
                dimension,
                natural_symbols,
                "structural dimension is not linear natural arithmetic",
            )?);
        }
    }
    Ok(lowered)
}

fn indexed_sequence_lengths<Metadata>(
    expression: &Expr<Metadata>,
    index: &Variable,
    variable_types: &BTreeMap<Variable, TypeExpr<()>>,
) -> Result<Vec<Expr<()>>, ShapeError> {
    struct Collector<'a> {
        index: &'a Variable,
        variable_types: &'a BTreeMap<Variable, TypeExpr<()>>,
        lengths: BTreeMap<Variable, Expr<()>>,
        error: Option<ShapeError>,
    }
    impl<Metadata> Visit<Metadata> for Collector<'_> {
        fn visit_raw_expr_binop(
            &mut self,
            op: &Binop,
            base: &Expr<Metadata>,
            subscript: &Expr<Metadata>,
        ) {
            if matches!(op, Binop::SingleSubscript)
                && matches!(&subscript.raw, RawExpr::Variable(variable) if variable == self.index)
            {
                let RawExpr::Variable(variable) = &base.raw else {
                    self.error = Some(ShapeError::Unsupported(
                        "sequence subscript base must be a variable".to_owned(),
                    ));
                    return;
                };
                let Some(TypeExpr::Seq(_, length)) = self.variable_types.get(variable) else {
                    self.error = Some(ShapeError::InvalidTyping(
                        "subscripted variable is not a sequence".to_owned(),
                    ));
                    return;
                };
                self.lengths.insert(variable.clone(), length.clone());
            }
            visit::visit_raw_expr_binop(self, op, base, subscript);
        }
    }

    let mut collector = Collector {
        index,
        variable_types,
        lengths: BTreeMap::new(),
        error: None,
    };
    collector.visit_expr(expression);
    if let Some(error) = collector.error {
        Err(error)
    } else {
        Ok(collector.lengths.into_values().collect())
    }
}

fn variable_z3_name(variable: &Variable) -> String {
    variable.z3_name()
}

fn collect_variables<Metadata>(
    expression: &Expr<Metadata>,
    variables: &mut BTreeSet<Variable>,
) -> Result<(), ShapeError> {
    struct Collector<'a> {
        variables: &'a mut BTreeSet<Variable>,
        active_binders: BTreeSet<Variable>,
        seen_binders: BTreeSet<Variable>,
        error: Option<ShapeError>,
    }
    impl<Metadata> Visit<Metadata> for Collector<'_> {
        fn visit_variable(&mut self, variable: &Variable) {
            if self.active_binders.contains(variable) {
                return;
            }
            if self.seen_binders.contains(variable) {
                self.error = Some(ShapeError::InvalidTyping(format!(
                    "sequence index {} collides with a free variable",
                    variable_z3_name(variable)
                )));
                return;
            }
            self.variables.insert(variable.clone());
        }

        fn visit_raw_expr_seqop(
            &mut self,
            _op: &SeqOp,
            range: &crate::Range<Metadata>,
            body: &Expr<Metadata>,
        ) {
            self.visit_expr(&range.from);
            self.visit_expr(&range.to);
            if self.active_binders.contains(&range.index_variable)
                || self.variables.contains(&range.index_variable)
            {
                self.error = Some(ShapeError::InvalidTyping(format!(
                    "sequence index {} collides with an enclosing or free variable",
                    variable_z3_name(&range.index_variable)
                )));
                return;
            }
            self.seen_binders.insert(range.index_variable.clone());
            self.active_binders.insert(range.index_variable.clone());
            self.visit_expr(body);
            self.active_binders.remove(&range.index_variable);
        }
    }
    let mut collector = Collector {
        variables,
        active_binders: BTreeSet::new(),
        seen_binders: BTreeSet::new(),
        error: None,
    };
    collector.visit_expr(expression);
    collector.error.map_or(Ok(()), Err)
}

fn collect_type_dimension_variables(ty: &TypeExpr<()>, variables: &mut BTreeSet<Variable>) {
    match ty {
        TypeExpr::Matrix(rows, cols) => {
            collect_variables(rows, variables)
                .expect("type dimensions cannot bind sequence indices");
            collect_variables(cols, variables)
                .expect("type dimensions cannot bind sequence indices");
        }
        TypeExpr::Seq(element, size) => {
            collect_variables(element, variables)
                .expect("type expressions cannot bind sequence indices");
            collect_variables(size, variables)
                .expect("type dimensions cannot bind sequence indices");
        }
        _ => {}
    }
}

fn collect_natural_position_variables<Metadata>(
    expression: &Expr<Metadata>,
    variables: &mut BTreeSet<Variable>,
) {
    struct Collector<'a>(&'a mut BTreeSet<Variable>);
    impl<Metadata> Visit<Metadata> for Collector<'_> {
        fn visit_raw_expr_type(&mut self, ty: &TypeExpr<Metadata>) {
            collect_type_dimension_variables(&ty.with_default_metadata(), self.0);
        }

        fn visit_raw_expr_standard_basis(
            &mut self,
            index: &Expr<Metadata>,
            _dimension: &ImplicitDimension,
        ) {
            collect_variables(index, self.0).expect("basis indices cannot bind sequence indices");
        }

        fn visit_raw_expr_binop(
            &mut self,
            op: &Binop,
            left: &Expr<Metadata>,
            right: &Expr<Metadata>,
        ) {
            self.visit_expr(left);
            if matches!(op, Binop::Power | Binop::SingleSubscript) {
                collect_variables(right, self.0)
                    .expect("natural operator operands cannot bind sequence indices");
            } else {
                self.visit_expr(right);
            }
        }

        fn visit_raw_expr_seqop(
            &mut self,
            _op: &SeqOp,
            range: &crate::Range<Metadata>,
            body: &Expr<Metadata>,
        ) {
            collect_variables(&range.from, self.0).expect("sequence bounds cannot bind indices");
            collect_variables(&range.to, self.0).expect("sequence bounds cannot bind indices");
            self.visit_expr(body);
        }
    }
    Collector(variables).visit_expr(expression);
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
        ShapeError, collect_implicit_dimensions, collect_variables, depends_on_implicit_dimension,
        dimension_equivalence_query, extract_environment_iterator,
        extract_environment_iterator_with_context, extract_prepared_environment_iterator,
        infer_symbolic_type_environment, type_depends_on_implicit,
    };
    use crate::{
        Annotation, Environment, Expr, Finop, ImplicitDimension, Matrix, NaturalParameter, Range,
        RawExpr, SeqOp, TypeExpr, Variable, from_tex, preprocessing::prepare_expression,
        type_resolver::SymbolicTypeEnvironment, visit_mut::VisitContext,
    };

    fn expression(tex: &str) -> Expr<()> {
        from_tex::expr(&parse(tex).unwrap()).unwrap()
    }

    fn environments(tex: &[&str]) -> super::EnvironmentIterator {
        extract_environment_iterator(tex.iter().map(|tex| expression(tex)), 10).unwrap()
    }

    fn natural(environment: &Environment, name: &str) -> u64 {
        environment.natural_assignment[&NaturalParameter::Variable(Variable::new(name))]
    }

    fn implicit(environment: &Environment, dimension: crate::ImplicitDimension) -> u64 {
        environment.natural_assignment[&NaturalParameter::ImplicitDimension(dimension)]
    }

    fn identity_dimension(expression: &Expr<()>) -> ImplicitDimension {
        let RawExpr::IdentityMatrix { dimension } = expression.raw else {
            panic!("expected an identity matrix")
        };
        dimension
    }

    #[test]
    fn dimension_equivalence_queries_are_unbounded_and_constraint_aware() {
        let left = expression("I");
        let right = expression("I");
        let left_dimension = identity_dimension(&left);
        let right_dimension = identity_dimension(&right);
        let types = SymbolicTypeEnvironment::default();
        let positive = VisitContext {
            logical_polarity: true,
            active_ranges: Vec::new(),
        };
        let unconstrained = [left.clone(), right.clone()]
            .iter()
            .map(|expression| prepare_expression(&types, expression, positive.clone()).unwrap())
            .collect::<Vec<_>>();
        let mut query = dimension_equivalence_query(&types, &[], &unconstrained).unwrap();
        assert_eq!(
            query.necessarily_equal(left_dimension, right_dimension),
            Some(false)
        );

        let one = Expr::new(RawExpr::Matrix(Matrix {
            rows: 1,
            cols: 1,
            elements: vec![Expr::new(RawExpr::NatLiteral(1))],
        }));
        let constrained = [left, right]
            .map(|identity| {
                Expr::new(RawExpr::CmpChain(crate::CmpChain {
                    start: identity,
                    assertions: vec![(crate::Cmp::Eq, one.clone())],
                }))
            })
            .iter()
            .map(|expression| prepare_expression(&types, expression, positive.clone()).unwrap())
            .collect::<Vec<_>>();
        let mut query = dimension_equivalence_query(&types, &[], &constrained).unwrap();
        assert_eq!(
            query.necessarily_equal(left_dimension, right_dimension),
            Some(true)
        );
    }

    fn concrete_type(
        environment: &Environment,
        types: &SymbolicTypeEnvironment,
        variable: &Variable,
    ) -> TypeExpr<()> {
        fn specialize(ty: &TypeExpr<()>, environment: &Environment) -> TypeExpr<()> {
            match ty {
                TypeExpr::Bool => TypeExpr::Bool,
                TypeExpr::Nat => TypeExpr::Nat,
                TypeExpr::Int => TypeExpr::Int,
                TypeExpr::Real => TypeExpr::Real,
                TypeExpr::Matrix(rows, cols) => matrix_type(
                    environment.evaluate_natural(rows).unwrap(),
                    environment.evaluate_natural(cols).unwrap(),
                ),
                TypeExpr::Seq(element, length) => {
                    let RawExpr::Type(element) = &element.raw else {
                        panic!("expected sequence element type")
                    };
                    TypeExpr::Seq(
                        Expr::new(RawExpr::Type(specialize(element, environment))),
                        Expr::new(RawExpr::NatLiteral(
                            environment.evaluate_natural(length).unwrap(),
                        )),
                    )
                }
            }
        }
        specialize(&types.types[variable], environment)
    }

    fn matrix_type(rows: u64, cols: u64) -> TypeExpr<()> {
        TypeExpr::Matrix(
            Expr::new(RawExpr::NatLiteral(rows)),
            Expr::new(RawExpr::NatLiteral(cols)),
        )
    }

    fn matrix_dimensions(ty: &TypeExpr<()>) -> Option<(u64, u64)> {
        let TypeExpr::Matrix(rows, cols) = ty else {
            return None;
        };
        let (RawExpr::NatLiteral(rows), RawExpr::NatLiteral(cols)) = (&rows.raw, &cols.raw) else {
            return None;
        };
        Some((*rows, *cols))
    }

    fn sequence_type(element: TypeExpr<()>, length: u64) -> TypeExpr<()> {
        TypeExpr::Seq(
            Expr::new(RawExpr::Type(element)),
            Expr::new(RawExpr::NatLiteral(length)),
        )
    }

    fn sequence_length(ty: &TypeExpr<()>) -> Option<u64> {
        let TypeExpr::Seq(_, length) = ty else {
            return None;
        };
        let RawExpr::NatLiteral(length) = length.raw else {
            return None;
        };
        Some(length)
    }

    fn inferred_types(tex: &[&str]) -> SymbolicTypeEnvironment {
        infer_symbolic_type_environment(&tex.iter().map(|tex| expression(tex)).collect::<Vec<_>>())
            .unwrap()
    }

    fn sequence(index: &str, body: Expr<()>) -> Expr<()> {
        Expr::new(RawExpr::Seqop(
            SeqOp::Sum,
            Range {
                index_variable: Variable::new(index),
                from: Expr::new(RawExpr::NatLiteral(1)),
                to: Expr::new(RawExpr::NatLiteral(2)),
            },
            body,
        ))
    }

    #[test]
    fn sequence_binders_reject_collisions_but_allow_sibling_reuse() {
        let variable = || Expr::new(RawExpr::Variable(Variable::new("i")));
        let nested = sequence("i", sequence("i", variable()));
        assert!(matches!(
            collect_variables(&nested, &mut BTreeSet::new()),
            Err(ShapeError::InvalidTyping(_))
        ));

        let global_collision = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![variable(), sequence("i", variable())],
        ));
        assert!(matches!(
            collect_variables(&global_collision, &mut BTreeSet::new()),
            Err(ShapeError::InvalidTyping(_))
        ));

        let siblings = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![sequence("i", variable()), sequence("i", variable())],
        ));
        let mut free = BTreeSet::new();
        collect_variables(&siblings, &mut free).unwrap();
        assert!(!free.contains(&Variable::new("i")));
    }

    #[test]
    fn implicit_dimension_provenance_is_preserved_in_symbolic_expressions() {
        let dimension = ImplicitDimension::fresh();
        let compound: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::ImplicitDimension(dimension)),
                Expr::new(RawExpr::NatLiteral(1)),
            ],
        ));
        let ordinary: Expr<()> = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::Variable(Variable::new("n"))),
                Expr::new(RawExpr::NatLiteral(1)),
            ],
        ));

        assert!(depends_on_implicit_dimension(&compound));
        assert!(type_depends_on_implicit(&TypeExpr::Matrix(
            compound,
            Expr::new(RawExpr::NatLiteral(1)),
        )));
        assert!(!depends_on_implicit_dimension(&ordinary));
    }

    #[test]
    fn guesses_types_and_respects_explicit_type_assertions() {
        let types = inferred_types(&[r"a = a", r"n = n", r"x \in \mathbb{R}"]);
        let environment = environments(&[r"a = a", r"n = n", r"x \in \mathbb{R}"])
            .next()
            .unwrap()
            .unwrap();
        assert_eq!(
            concrete_type(&environment, &types, &Variable::new("a")),
            TypeExpr::Real
        );
        assert_eq!(
            concrete_type(&environment, &types, &Variable::new("n")),
            TypeExpr::Nat
        );
        assert_eq!(
            concrete_type(&environment, &types, &Variable::new("x")),
            TypeExpr::Real
        );
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
                        active_ranges: Vec::new(),
                    },
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let environments = extract_prepared_environment_iterator(&types, &prepared, &[], 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(environments.len(), 2);
        assert!(environments.iter().all(|environment| {
            matches!(matrix_dimensions(&concrete_type(environment, &types, &Variable::new("A"))), Some((rows, cols)) if rows == cols)
        }));
    }

    #[test]
    fn pointwise_generated_definitions_preserve_sequence_binders() {
        let assumptions = vec![
            expression(r"\lambda \in \operatorname{Seq}_{n}(\mathbb{R})"),
            expression(r"\sum_{i=1}^{n}\lambda_i^{\frac{1}{2}} \ge 0"),
        ];
        let types = infer_symbolic_type_environment(&assumptions).unwrap();
        let prepared = assumptions
            .iter()
            .map(|expression| {
                prepare_expression(&types, expression, VisitContext::positive()).unwrap()
            })
            .collect::<Vec<_>>();
        let environments = extract_prepared_environment_iterator(&types, &prepared, &[], 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(
            environments
                .iter()
                .map(|environment| natural(environment, "n"))
                .collect::<Vec<_>>(),
            [1, 2]
        );
    }

    #[test]
    fn dependent_sequence_dimensions_are_checked_for_every_active_position() {
        let n = Variable::new("n");
        let types = SymbolicTypeEnvironment {
            types: std::collections::HashMap::from([
                (n.clone(), TypeExpr::Nat),
                (
                    Variable::new("A"),
                    TypeExpr::Seq(
                        Expr::new(RawExpr::Type(TypeExpr::Matrix(
                            Expr::new(RawExpr::BoundNatural(0)),
                            Expr::new(RawExpr::NatLiteral(1)),
                        ))),
                        Expr::new(RawExpr::Variable(n.clone())),
                    ),
                ),
            ]),
        };
        let assertion = expression(r"\sum_{i=1}^{n}\det(A_i) = 0");
        let prepared = prepare_expression(&types, &assertion, VisitContext::positive()).unwrap();
        let environments = extract_prepared_environment_iterator(&types, &[prepared], &[], 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(environments.len(), 1);
        assert_eq!(natural(&environments[0], "n"), 1);
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
                            active_ranges: Vec::new(),
                        },
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let environments = extract_prepared_environment_iterator(&types, &prepared, &[], 2)
                .unwrap()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(environments.len(), 2);
            assert!(environments.iter().all(|environment| {
                matches!(
                    matrix_dimensions(&concrete_type(environment, &types, &Variable::new("A"))),
                    Some((_, 1))
                )
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
        assert_eq!(natural(&environment, "m"), 1);
        assert_eq!(natural(&environment, "n"), 1);
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
        assert_eq!(natural(&environment, "m"), 1);
        assert_eq!(natural(&environment, "n"), 1);
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
        let types = inferred_types(&[r"A \in \mathbb{R}^{n \times d + p}"]);
        let mut environments = environments(&[r"A \in \mathbb{R}^{n \times d + p}"]);
        let first = environments.next().unwrap().unwrap();
        assert_eq!(
            concrete_type(&first, &types, &Variable::new("A")),
            matrix_type(1, 1)
        );

        let next_assignments: Vec<_> = environments
            .take(3)
            .map(|result| {
                let environment = result.unwrap();
                (
                    natural(&environment, "n"),
                    natural(&environment, "d"),
                    natural(&environment, "p"),
                    concrete_type(&environment, &types, &Variable::new("A")),
                )
            })
            .collect();
        assert_eq!(next_assignments.len(), 3);
        let sums = next_assignments
            .iter()
            .map(|(n, d, p, _)| n + d + p)
            .collect::<Vec<_>>();
        assert!(sums.windows(2).all(|pair| pair[0] <= pair[1]));
    }

    #[test]
    fn enumeration_extends_coordinatewise_dimension_order() {
        let shapes = extract_environment_iterator([expression("U = U")].into_iter(), 2)
            .unwrap()
            .map(|environment| {
                let environment = environment.unwrap();
                let types = inferred_types(&["U = U"]);
                let Some((rows, cols)) =
                    matrix_dimensions(&concrete_type(&environment, &types, &Variable::new("U")))
                else {
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
        let inferred = inferred_types(&[r"\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})"]);
        let types: Vec<_> = environments
            .iter()
            .map(|environment| concrete_type(environment, &inferred, &z))
            .collect();
        assert_eq!(types.len(), 4);
        assert!(types.contains(&sequence_type(matrix_type(1, 1), 1)));
        assert!(types.contains(&sequence_type(matrix_type(2, 1), 2)));
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
                    natural(environment, "a"),
                    natural(environment, "b"),
                    sequence_length(&concrete_type(
                        environment,
                        &inferred_types(&[
                            r"\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R})",
                            r"\sum_{i=a}^{b} \vec{z}_i = 0",
                        ]),
                        &z,
                    ))
                    .expect("expected a sequence"),
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
            natural(environment, "A_{rows}") <= 2 && natural(environment, "A_{cols}") <= 2
        }));
    }

    #[test]
    fn reports_whether_the_dimension_bound_is_exhaustive() {
        let dimensionless =
            extract_environment_iterator([expression("a = a")].into_iter(), 0).unwrap();
        assert!(dimensionless.dimension_bound_is_exhaustive());

        let fixed = extract_environment_iterator(
            [expression(r"A \in \mathbb{R}^{2 \times 2}")].into_iter(),
            2,
        )
        .unwrap();
        assert!(fixed.dimension_bound_is_exhaustive());

        let unconstrained =
            extract_environment_iterator([expression("A = A")].into_iter(), 2).unwrap();
        assert!(!unconstrained.dimension_bound_is_exhaustive());

        let gapped = extract_environment_iterator(
            [expression(r"A \in \mathbb{R}^{4 \times 4}")].into_iter(),
            2,
        )
        .unwrap();
        assert!(!gapped.dimension_bound_is_exhaustive());
        assert_eq!(gapped.count(), 0);
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
    fn complete_assignments_include_auxiliary_naturals() {
        let assignments: Vec<_> =
            environments(&[r"A \in \mathbb{R}^{n}", r"p \in \mathbb{N}", r"p = p"])
                .take(3)
                .map(|result| {
                    let environment = result.unwrap();
                    (natural(&environment, "n"), natural(&environment, "p"))
                })
                .collect();
        assert_eq!(assignments[0], (1, 0));
        assert_eq!(
            assignments[1..].iter().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([(1, 1), (2, 0)])
        );
    }

    #[test]
    fn implicit_matrix_constraints_restrict_environments() {
        let environment =
            environments(&[r"A B = \begin{bmatrix}1 & 2 & 3 \\ 4 & 5 & 6\end{bmatrix}"])
                .next()
                .unwrap()
                .unwrap();
        let a_rows = natural(&environment, "A_{rows}");
        let a_cols = natural(&environment, "A_{cols}");
        let b_rows = natural(&environment, "B_{rows}");
        let b_cols = natural(&environment, "B_{cols}");
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
                    .map(|dimension| implicit(&environment, dimension))
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
                .map(|dimension| implicit(&environment, *dimension))
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
            natural(&environment, "A_{cols}") != natural(&environment, "B_{rows}")
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
        assert_eq!(natural(&valid, "i"), 2);

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
        assert_eq!(symbolic.evaluate_natural(index).unwrap(), 2);

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
        assert_eq!(natural(&environment, "n"), 3);
    }

    #[test]
    fn preserves_known_natural_equalities_in_environments() {
        let environment = environments(&[r"k = 2"]).next().unwrap().unwrap();
        assert_eq!(natural(&environment, "k"), 2);
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
            Err(ShapeError::Unsat(_))
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
        let types = inferred_types(&valid);
        assert_eq!(
            concrete_type(&environments[0], &types, &Variable::new("M")),
            matrix_type(3, 3)
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
                .natural_assignment
                .iter()
                .all(|(parameter, value)| {
                    !matches!(parameter, NaturalParameter::ImplicitDimension(_)) || *value == 1
                })
        );
    }

    #[test]
    fn block_selector_uniquely_infers_context_dependent_dimensions() {
        let assumptions = [
            r"A \in \mathbb{R}^{2 \times 2}",
            r"B \in \mathbb{R}^{2 \times 2}",
            r"\begin{bmatrix}A & B\end{bmatrix} \begin{bmatrix}I \\ \mathbb{0}\end{bmatrix} = A",
        ];
        let environments = extract_environment_iterator(assumptions.into_iter().map(expression), 2)
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        assert_eq!(environments.len(), 1);
        let implicit_values = environments[0]
            .natural_assignment
            .iter()
            .filter_map(|(parameter, value)| {
                matches!(parameter, NaturalParameter::ImplicitDimension(_)).then_some(*value)
            })
            .collect::<Vec<_>>();
        assert_eq!(implicit_values.len(), 3);
        assert!(implicit_values.iter().all(|dimension| *dimension == 2));
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
            let types = inferred_types(&[assertion]);
            let environment = extract_environment_iterator([expression(assertion)].into_iter(), 2)
                .unwrap()
                .next()
                .unwrap()
                .unwrap();
            let Some((rows, cols)) =
                matrix_dimensions(&concrete_type(&environment, &types, &Variable::new("A")))
            else {
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
