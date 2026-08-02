use crate::{
    Environment, Expr, enumerable_assignments_to_naturals::NaturalsWithComparisonAndEquality,
};

fn extract_explicit_and_implicit_constraints<Metadata>(
    assumptions: impl Iterator<Item = Expr<Metadata>>,
) -> NaturalsWithComparisonAndEquality {
    todo!()
}

pub fn extract_environment_iterator<Metadata>(
    assumptions: impl Iterator<Item = Expr<Metadata>>,
) -> impl Iterator<Item = Environment> {
    todo!()
}
