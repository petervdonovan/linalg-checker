use std::collections::BTreeMap;

use crate::{
    Binop, Cmp, CmpChain, Expr, Finop, Monop, RawExpr, TypeExpr, Variable,
    deep_clone::deep_clone,
    type_resolver::{MaybeTyped, TypeError},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Default)]
pub struct Norm2SquaredVisitor {
    rewrites: usize,
    error: Option<TypeError>,
}

impl Norm2SquaredVisitor {
    pub fn finish(self) -> Result<usize, TypeError> {
        self.error.map_or(Ok(self.rewrites), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2SquaredVisitor
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let Some(operand) = norm2_squared_operand(node) else {
            return;
        };
        if let Ok(ty) = operand.meta.get_type()
            && !matches!(ty, TypeExpr::Matrix(_, _))
        {
            self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
            return;
        }
        let mut core = norm2_squared(operand);
        let raw = std::mem::replace(
            &mut core
                .get_mut()
                .expect("newly constructed 2-norm core must be uniquely owned")
                .raw,
            RawExpr::Hole,
        );
        node.get_mut()
            .expect("2-norm lowering requires uniquely owned expressions")
            .raw = raw;
        self.rewrites += 1;
    }
}

pub struct Norm2Visitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    rewrites: usize,
    error: Option<TypeError>,
}

impl<Metadata> Default for Norm2Visitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            rewrites: 0,
            error: None,
        }
    }
}

impl<Metadata> Norm2Visitor<Metadata> {
    pub fn finish(self) -> Result<(usize, Vec<SideCondition<Metadata>>), TypeError> {
        self.error
            .map_or(Ok((self.rewrites, self.roots.side_conditions)), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2Visitor<Metadata>
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        std::mem::take(&mut self.roots.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let RawExpr::Monop(Monop::Norm2, operand) = &node.raw else {
            return;
        };
        if let Ok(ty) = operand.meta.get_type()
            && !matches!(ty, TypeExpr::Matrix(_, _))
        {
            self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
            return;
        }
        let radicand = norm2_squared(operand);
        let introduced =
            self.roots
                .lower(node, radicand, TypeExpr::Real, RootExistence::Guaranteed);
        node.get_mut()
            .expect("2-norm lowering requires uniquely owned expressions")
            .raw = RawExpr::Variable(introduced);
        self.rewrites += 1;
    }
}

pub struct SquareRootVisitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    error: Option<TypeError>,
    rewrites: usize,
}

impl<Metadata> Default for SquareRootVisitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            error: None,
            rewrites: 0,
        }
    }
}

impl<Metadata> SquareRootVisitor<Metadata> {
    pub fn finish(self) -> Result<(usize, Vec<SideCondition<Metadata>>), TypeError> {
        self.error
            .map_or(Ok((self.rewrites, self.roots.side_conditions)), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for SquareRootVisitor<Metadata>
where
    Metadata: Clone + Default + MaybeTyped,
{
    fn side_conditions(&mut self) -> Vec<SideCondition<Metadata>> {
        std::mem::take(&mut self.roots.side_conditions)
    }

    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        if !is_square_root(node) {
            return;
        }
        let RawExpr::Binop(Binop::Power, base, _) = &node.raw else {
            unreachable!()
        };
        let ty = match base.meta.get_type() {
            Ok(TypeExpr::Real) => TypeExpr::Real,
            Ok(matrix @ TypeExpr::Matrix(_, _)) => matrix,
            Ok(_) => {
                self.error = Some(TypeError::Invalid(
                    "square root requires a real scalar or square real matrix",
                ));
                return;
            }
            Err(_) => return,
        };
        let existence = match ty {
            TypeExpr::Real => RootExistence::Checkable,
            TypeExpr::Matrix(_, _) => RootExistence::Assumed,
            _ => unreachable!(),
        };
        let introduced = self.roots.lower(node, deep_clone(base), ty, existence);
        node.get_mut()
            .expect("square-root lowering requires uniquely owned expressions")
            .raw = RawExpr::Variable(introduced);
        self.rewrites += 1;
    }
}

#[derive(Clone, Copy)]
enum RootExistence {
    Guaranteed,
    Checkable,
    Assumed,
}

struct PrincipalRootRegistry<Metadata> {
    side_conditions: Vec<SideCondition<Metadata>>,
    by_variable: BTreeMap<Variable, usize>,
}

impl<Metadata> Default for PrincipalRootRegistry<Metadata> {
    fn default() -> Self {
        Self {
            side_conditions: Vec::new(),
            by_variable: BTreeMap::new(),
        }
    }
}

impl<Metadata> PrincipalRootRegistry<Metadata>
where
    Metadata: Clone + Default,
{
    fn lower(
        &mut self,
        source: &Expr<Metadata>,
        radicand: Expr<Metadata>,
        ty: TypeExpr<()>,
        existence: RootExistence,
    ) -> Variable {
        let introduced_variable = Variable::new(source.as_latex_verbose().to_string());
        // These wrappers are new syntax nodes, so the source node's metadata
        // does not describe them. Type resolution fills their default metadata.
        let introduced = Expr::with_metadata(
            Metadata::default(),
            RawExpr::Variable(introduced_variable.clone()),
        );
        let square = Expr::with_metadata(
            Metadata::default(),
            RawExpr::Finop(
                Finop::Times,
                vec![deep_clone(&introduced), deep_clone(&introduced)],
            ),
        );
        let mut defining_assertions = vec![comparison(square, Cmp::Eq, deep_clone(&radicand))];
        if matches!(ty, TypeExpr::Real) {
            defining_assertions.push(comparison(deep_clone(&introduced), Cmp::Ge, natural(0)));
        }
        let existence = match existence {
            RootExistence::Guaranteed => Existence::Guaranteed,
            RootExistence::Checkable => {
                Existence::Checkable(vec![comparison(radicand, Cmp::Lt, natural(0))])
            }
            RootExistence::Assumed => Existence::Assumed,
        };
        let condition = SideCondition {
            introduced_variable: introduced_variable.clone(),
            display_name: source.as_latex().to_string(),
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
        introduced_variable
    }
}

fn norm2_squared_operand<Metadata>(expression: &Expr<Metadata>) -> Option<&Expr<Metadata>> {
    let RawExpr::Binop(Binop::Power, norm, exponent) = &expression.raw else {
        return None;
    };
    let RawExpr::Monop(Monop::Norm2, operand) = &norm.raw else {
        return None;
    };
    matches!(exponent.raw, RawExpr::NatLiteral(2)).then_some(operand)
}

fn norm2_squared<Metadata>(operand: &Expr<Metadata>) -> Expr<Metadata>
where
    Metadata: Clone + Default,
{
    let transpose = Expr::with_metadata(
        Metadata::default(),
        RawExpr::Monop(Monop::Transpose, deep_clone(operand)),
    );
    let product = Expr::with_metadata(
        Metadata::default(),
        RawExpr::Finop(Finop::Times, vec![transpose, deep_clone(operand)]),
    );
    Expr::with_metadata(
        Metadata::default(),
        RawExpr::Binop(
            Binop::Cast,
            Expr::with_metadata(Metadata::default(), RawExpr::Type(TypeExpr::Real)),
            product,
        ),
    )
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

fn comparison<Metadata: Default>(
    left: Expr<Metadata>,
    op: Cmp,
    right: Expr<Metadata>,
) -> Expr<Metadata> {
    Expr::with_metadata(
        Metadata::default(),
        RawExpr::CmpChain(CmpChain {
            start: left,
            assertions: vec![(op, right)],
        }),
    )
}

fn natural<Metadata: Default>(value: u64) -> Expr<Metadata> {
    Expr::with_metadata(Metadata::default(), RawExpr::NatLiteral(value))
}

pub(crate) fn assert_compatible<Metadata>(
    previous: &SideCondition<Metadata>,
    current: &SideCondition<Metadata>,
) {
    assert_eq!(previous.introduced_type, current.introduced_type);
    assert_eq!(previous.display_name, current.display_name);
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
    match (&previous.existence, &current.existence) {
        (Existence::Guaranteed, Existence::Guaranteed)
        | (Existence::Assumed, Existence::Assumed) => {}
        (Existence::Checkable(previous), Existence::Checkable(current)) => assert_eq!(
            render(previous),
            render(current),
            "same-named synthetic variables have incompatible existence checks"
        ),
        _ => panic!("same-named synthetic variables have incompatible existence classes"),
    }
}
