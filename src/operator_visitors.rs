use std::collections::BTreeMap;

use crate::{
    Binop, Cmp, CmpChain, Expr, Finop, RawExpr, Type, Variable,
    deep_clone::deep_clone,
    type_resolver::{MaybeTyped, TypeError, concrete_type_expr},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

pub struct SquareRootVisitor<Metadata> {
    side_conditions: Vec<SideCondition<Metadata>>,
    by_variable: BTreeMap<Variable, usize>,
    error: Option<TypeError>,
}

impl<Metadata> Default for SquareRootVisitor<Metadata> {
    fn default() -> Self {
        Self {
            side_conditions: Vec::new(),
            by_variable: BTreeMap::new(),
            error: None,
        }
    }
}

impl<Metadata> SquareRootVisitor<Metadata> {
    pub fn finish(mut self) -> Result<Vec<SideCondition<Metadata>>, TypeError>
    where
        Metadata: Clone + MaybeTyped,
    {
        if let Some(error) = self.error.take() {
            Err(error)
        } else {
            Ok(self.side_conditions())
        }
    }
}

impl<Metadata> VisitMut<Metadata> for SquareRootVisitor<Metadata>
where
    Metadata: Clone + MaybeTyped,
{
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        std::mem::take(&mut self.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        if !is_square_root(node) {
            return;
        }
        let root_name = node.as_latex().to_string();
        let ty = match node
            .meta
            .get_type()
            .and_then(|ty| concrete_type_expr(&ty))
        {
            Ok(Type::Real) => Type::Real,
            Ok(Type::Matrix(rows, cols)) if rows == cols => Type::Matrix(rows, cols),
            Ok(Type::Matrix(_, _)) => {
                self.error = Some(TypeError::Invalid("matrix square root requires a square matrix"));
                return;
            }
            Ok(_) => {
                self.error = Some(TypeError::Invalid(
                    "square root requires a real scalar or square real matrix",
                ));
                return;
            }
            Err(error) => {
                self.error = Some(error);
                return;
            }
        };
        let RawExpr::Binop(Binop::Power, base, _) = &node.raw else {
            unreachable!()
        };
        let base = deep_clone(base);
        let introduced_variable = Variable::new(root_name);
        let introduced = Expr::with_metadata(
            node.meta.clone(),
            RawExpr::Variable(introduced_variable.clone()),
        );
        let square = Expr::with_metadata(
            node.meta.clone(),
            RawExpr::Finop(
                Finop::Times,
                vec![deep_clone(&introduced), deep_clone(&introduced)],
            ),
        );
        let mut defining_assertions = vec![comparison(
            node.meta.clone(),
            square,
            Cmp::Eq,
            deep_clone(&base),
        )];
        let existence = match ty {
            Type::Real => {
                defining_assertions.push(comparison(
                    node.meta.clone(),
                    deep_clone(&introduced),
                    Cmp::Ge,
                    natural(node.meta.clone(), 0),
                ));
                Existence::Checkable(vec![comparison(
                    node.meta.clone(),
                    base,
                    Cmp::Lt,
                    natural(node.meta.clone(), 0),
                )])
            }
            Type::Matrix(_, _) => Existence::Assumed,
            _ => unreachable!(),
        };
        let condition = SideCondition {
            introduced_variable: introduced_variable.clone(),
            introduced_type: ty,
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
        node.get_mut()
            .expect("square-root lowering requires uniquely owned expressions")
            .raw = RawExpr::Variable(introduced_variable);
    }
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

fn comparison<Metadata>(
    metadata: Metadata,
    left: Expr<Metadata>,
    op: Cmp,
    right: Expr<Metadata>,
) -> Expr<Metadata> {
    Expr::with_metadata(
        metadata,
        RawExpr::CmpChain(CmpChain {
            start: left,
            assertions: vec![(op, right)],
        }),
    )
}

fn natural<Metadata>(metadata: Metadata, value: u64) -> Expr<Metadata> {
    Expr::with_metadata(metadata, RawExpr::NatLiteral(value))
}

fn assert_compatible<Metadata>(
    previous: &SideCondition<Metadata>,
    current: &SideCondition<Metadata>,
) {
    assert_eq!(previous.introduced_type, current.introduced_type);
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
}
