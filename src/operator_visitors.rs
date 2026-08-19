use std::collections::BTreeMap;

use crate::{
    Binop, Cmp, CmpChain, Expr, Finop, Monop, RawExpr, TypeExpr, Variable,
    deep_clone::deep_clone,
    type_resolver::{MaybeTyped, TypeError},
    visit_mut::{self, Existence, SideCondition, VisitContext, VisitMut},
};

#[derive(Default)]
pub struct Norm2SquaredVisitor {
    error: Option<TypeError>,
}

impl Norm2SquaredVisitor {
    pub fn finish(self) -> Result<(), TypeError> {
        self.error.map_or(Ok(()), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2SquaredVisitor
where
    Metadata: Clone + MaybeTyped,
{
    fn visit_expr_mut(&mut self, context: VisitContext, node: &mut Expr<Metadata>) {
        if self.error.is_some() {
            return;
        }
        visit_mut::visit_expr_mut(self, context, node);
        let Some(operand) = norm2_squared_operand(node) else {
            return;
        };
        match operand.meta.get_type() {
            Ok(TypeExpr::Matrix(_, _)) => {}
            Ok(_) => {
                self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
                return;
            }
            Err(error) => {
                self.error = Some(error);
                return;
            }
        }
        let mut core = norm2_squared(node.meta.clone(), operand);
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
    }
}

pub struct Norm2Visitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    error: Option<TypeError>,
}

impl<Metadata> Default for Norm2Visitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            error: None,
        }
    }
}

impl<Metadata> Norm2Visitor<Metadata> {
    pub fn finish(self) -> Result<Vec<SideCondition<Metadata>>, TypeError> {
        self.error.map_or(Ok(self.roots.side_conditions), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for Norm2Visitor<Metadata>
where
    Metadata: Clone + MaybeTyped,
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
        match operand.meta.get_type() {
            Ok(TypeExpr::Matrix(_, _)) => {}
            Ok(_) => {
                self.error = Some(TypeError::Invalid("2-norm requires a real column matrix"));
                return;
            }
            Err(error) => {
                self.error = Some(error);
                return;
            }
        }
        let radicand = norm2_squared(node.meta.clone(), operand);
        let introduced =
            self.roots
                .lower(node, radicand, TypeExpr::Real, RootExistence::Guaranteed);
        node.get_mut()
            .expect("2-norm lowering requires uniquely owned expressions")
            .raw = RawExpr::Variable(introduced);
    }
}

pub struct SquareRootVisitor<Metadata> {
    roots: PrincipalRootRegistry<Metadata>,
    error: Option<TypeError>,
}

impl<Metadata> Default for SquareRootVisitor<Metadata> {
    fn default() -> Self {
        Self {
            roots: PrincipalRootRegistry::default(),
            error: None,
        }
    }
}

impl<Metadata> SquareRootVisitor<Metadata> {
    pub fn finish(self) -> Result<Vec<SideCondition<Metadata>>, TypeError> {
        self.error.map_or(Ok(self.roots.side_conditions), Err)
    }
}

impl<Metadata> VisitMut<Metadata> for SquareRootVisitor<Metadata>
where
    Metadata: Clone + MaybeTyped,
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
        let ty = match node.meta.get_type() {
            Ok(TypeExpr::Real) => TypeExpr::Real,
            Ok(matrix @ TypeExpr::Matrix(_, _)) => matrix,
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
        let existence = match ty {
            TypeExpr::Real => RootExistence::Checkable,
            TypeExpr::Matrix(_, _) => RootExistence::Assumed,
            _ => unreachable!(),
        };
        let introduced = self.roots.lower(node, deep_clone(base), ty, existence);
        node.get_mut()
            .expect("square-root lowering requires uniquely owned expressions")
            .raw = RawExpr::Variable(introduced);
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
    Metadata: Clone + MaybeTyped,
{
    fn lower(
        &mut self,
        source: &Expr<Metadata>,
        radicand: Expr<Metadata>,
        ty: TypeExpr<()>,
        existence: RootExistence,
    ) -> Variable {
        let introduced_variable = Variable::new(source.as_latex_verbose().to_string());
        let introduced = Expr::with_metadata(
            source.meta.clone(),
            RawExpr::Variable(introduced_variable.clone()),
        );
        let square = Expr::with_metadata(
            source.meta.clone(),
            RawExpr::Finop(
                Finop::Times,
                vec![deep_clone(&introduced), deep_clone(&introduced)],
            ),
        );
        let mut defining_assertions = vec![comparison(
            source.meta.clone(),
            square,
            Cmp::Eq,
            deep_clone(&radicand),
        )];
        if matches!(ty, TypeExpr::Real) {
            defining_assertions.push(comparison(
                source.meta.clone(),
                deep_clone(&introduced),
                Cmp::Ge,
                natural(source.meta.clone(), 0),
            ));
        }
        let existence = match existence {
            RootExistence::Guaranteed => Existence::Guaranteed,
            RootExistence::Checkable => Existence::Checkable(vec![comparison(
                source.meta.clone(),
                radicand,
                Cmp::Lt,
                natural(source.meta.clone(), 0),
            )]),
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

fn norm2_squared<Metadata>(metadata: Metadata, operand: &Expr<Metadata>) -> Expr<Metadata>
where
    Metadata: Clone + MaybeTyped,
{
    let TypeExpr::Matrix(rows, cols) = operand
        .meta
        .get_type()
        .expect("2-norm operand type was checked before constructing its core expression")
    else {
        unreachable!()
    };
    let transpose = typed(
        metadata.clone(),
        TypeExpr::Matrix(cols.clone(), rows),
        RawExpr::Monop(Monop::Transpose, deep_clone(operand)),
    );
    let product = typed(
        metadata.clone(),
        TypeExpr::Matrix(cols.clone(), cols),
        RawExpr::Finop(Finop::Times, vec![transpose, deep_clone(operand)]),
    );
    typed(
        metadata.clone(),
        TypeExpr::Real,
        RawExpr::Binop(
            Binop::Cast,
            Expr::with_metadata(metadata, RawExpr::Type(TypeExpr::Real)),
            product,
        ),
    )
}

fn typed<Metadata: MaybeTyped>(
    mut metadata: Metadata,
    ty: TypeExpr<()>,
    raw: RawExpr<Metadata>,
) -> Expr<Metadata> {
    metadata.put_type(ty);
    Expr::with_metadata(metadata, raw)
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
