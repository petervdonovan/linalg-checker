use crate::{
    Expr, RawExpr, TypeExpr, Variable,
    deep_clone::deep_clone,
    visit_mut::{self, VisitContext, VisitMut},
};

struct ShiftBoundNaturals {
    cutoff: usize,
    amount: usize,
}

impl VisitMut<()> for ShiftBoundNaturals {
    fn visit_raw_expr_bound_natural_mut(&mut self, _context: VisitContext, depth: &mut usize) {
        if *depth >= self.cutoff {
            *depth += self.amount;
        }
    }

    fn visit_type_expr_mut(&mut self, context: VisitContext, ty: &mut TypeExpr<()>) {
        match ty {
            TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
            TypeExpr::Matrix(rows, cols) => {
                self.visit_expr_mut(context.clone(), rows);
                self.visit_expr_mut(context, cols);
            }
            TypeExpr::Seq(element, length) => {
                self.visit_expr_mut(context.clone(), length);
                self.cutoff += 1;
                self.visit_expr_mut(context, element);
                self.cutoff -= 1;
            }
        }
    }
}

fn shift_expression(expression: &Expr<()>, amount: usize) -> Expr<()> {
    let mut result = deep_clone(expression);
    ShiftBoundNaturals { cutoff: 0, amount }.visit_expr_mut(VisitContext::positive(), &mut result);
    result
}

struct AbstractVariable<'a> {
    variable: &'a Variable,
    replacement: &'a Expr<()>,
    depth: usize,
}

impl VisitMut<()> for AbstractVariable<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, expression: &mut Expr<()>) {
        if matches!(&expression.raw, RawExpr::Variable(variable) if variable == self.variable) {
            *expression = shift_expression(self.replacement, self.depth);
        } else {
            visit_mut::visit_expr_mut(self, context, expression);
        }
    }

    fn visit_type_expr_mut(&mut self, context: VisitContext, ty: &mut TypeExpr<()>) {
        match ty {
            TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
            TypeExpr::Matrix(rows, cols) => {
                self.visit_expr_mut(context.clone(), rows);
                self.visit_expr_mut(context, cols);
            }
            TypeExpr::Seq(element, length) => {
                self.visit_expr_mut(context.clone(), length);
                self.depth += 1;
                self.visit_expr_mut(context, element);
                self.depth -= 1;
            }
        }
    }
}

pub(crate) fn abstract_type_variable(
    ty: &TypeExpr<()>,
    variable: &Variable,
    replacement: &Expr<()>,
) -> TypeExpr<()> {
    let mut expression: Expr<()> = Expr::new(RawExpr::Type(ty.clone())).with_default_metadata();
    AbstractVariable {
        variable,
        replacement,
        depth: 0,
    }
    .visit_expr_mut(VisitContext::positive(), &mut expression);
    let RawExpr::Type(ty) = &expression.raw else {
        unreachable!()
    };
    ty.clone()
}

struct OpenBoundNatural<'a> {
    replacement: &'a Expr<()>,
    depth: usize,
}

impl VisitMut<()> for OpenBoundNatural<'_> {
    fn visit_expr_mut(&mut self, context: VisitContext, expression: &mut Expr<()>) {
        let RawExpr::BoundNatural(index) = expression.raw else {
            visit_mut::visit_expr_mut(self, context, expression);
            return;
        };
        if index == self.depth {
            *expression = shift_expression(self.replacement, self.depth);
        } else if index > self.depth {
            expression.get_mut().unwrap().raw = RawExpr::BoundNatural(index - 1);
        }
    }

    fn visit_type_expr_mut(&mut self, context: VisitContext, ty: &mut TypeExpr<()>) {
        match ty {
            TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
            TypeExpr::Matrix(rows, cols) => {
                self.visit_expr_mut(context.clone(), rows);
                self.visit_expr_mut(context, cols);
            }
            TypeExpr::Seq(element, length) => {
                self.visit_expr_mut(context.clone(), length);
                self.depth += 1;
                self.visit_expr_mut(context, element);
                self.depth -= 1;
            }
        }
    }
}

pub(crate) fn open_sequence_element(ty: &TypeExpr<()>, position: &Expr<()>) -> TypeExpr<()> {
    let mut expression: Expr<()> = Expr::new(RawExpr::Type(ty.clone())).with_default_metadata();
    OpenBoundNatural {
        replacement: position,
        depth: 0,
    }
    .visit_expr_mut(VisitContext::positive(), &mut expression);
    let RawExpr::Type(ty) = &expression.raw else {
        unreachable!()
    };
    ty.clone()
}

pub(crate) fn substitute_type_variable(
    ty: &TypeExpr<()>,
    variable: &Variable,
    replacement: &Expr<()>,
) -> TypeExpr<()> {
    let abstracted = abstract_type_variable(ty, variable, &Expr::new(RawExpr::BoundNatural(0)));
    open_sequence_element(&abstracted, replacement)
}

pub(crate) fn contains_unbound_natural(ty: &TypeExpr<()>) -> bool {
    struct Finder {
        depth: usize,
        found: bool,
    }
    impl VisitMut<()> for Finder {
        fn visit_raw_expr_bound_natural_mut(&mut self, _context: VisitContext, index: &mut usize) {
            self.found |= *index >= self.depth;
        }
        fn visit_type_expr_mut(&mut self, context: VisitContext, ty: &mut TypeExpr<()>) {
            match ty {
                TypeExpr::Bool | TypeExpr::Nat | TypeExpr::Int | TypeExpr::Real => {}
                TypeExpr::Matrix(rows, cols) => {
                    self.visit_expr_mut(context.clone(), rows);
                    self.visit_expr_mut(context, cols);
                }
                TypeExpr::Seq(element, length) => {
                    self.visit_expr_mut(context.clone(), length);
                    self.depth += 1;
                    self.visit_expr_mut(context, element);
                    self.depth -= 1;
                }
            }
        }
    }
    let mut expression: Expr<()> = Expr::new(RawExpr::Type(ty.clone())).with_default_metadata();
    let mut finder = Finder {
        depth: 0,
        found: false,
    };
    finder.visit_expr_mut(VisitContext::positive(), &mut expression);
    finder.found
}

pub(crate) fn expression_contains_bound_natural<Metadata>(expression: &Expr<Metadata>) -> bool {
    struct Finder(bool);
    impl<Metadata> crate::visit::Visit<Metadata> for Finder {
        fn visit_raw_expr_bound_natural(&mut self, _depth: &usize) {
            self.0 = true;
        }
    }
    let mut finder = Finder(false);
    crate::visit::Visit::visit_expr(&mut finder, expression);
    finder.0
}

#[cfg(test)]
mod tests {
    use super::{abstract_type_variable, contains_unbound_natural, open_sequence_element};
    use crate::{Environment, Expr, Finop, Monop, RawExpr, TypeExpr, Variable};

    #[test]
    fn abstracts_and_opens_shifted_sequence_positions() {
        let index = Variable::new("i");
        let ty = TypeExpr::Matrix(
            Expr::new(RawExpr::Variable(index.clone())),
            Expr::new(RawExpr::NatLiteral(1)),
        );
        let source_position = Expr::new(RawExpr::Finop(
            Finop::Plus,
            vec![
                Expr::new(RawExpr::NatLiteral(2)),
                Expr::new(RawExpr::BoundNatural(0)),
                Expr::new(RawExpr::Monop(
                    Monop::Neg,
                    Expr::new(RawExpr::NatLiteral(1)),
                )),
            ],
        ));
        let abstracted = abstract_type_variable(&ty, &index, &source_position);
        assert!(contains_unbound_natural(&abstracted));
        let opened = open_sequence_element(&abstracted, &Expr::new(RawExpr::NatLiteral(3)));
        let TypeExpr::Matrix(rows, _) = opened else {
            panic!("expected a matrix type")
        };
        assert_eq!(Environment::default().evaluate_natural(&rows), Ok(4));
        assert!(!contains_unbound_natural(&TypeExpr::Matrix(
            rows,
            Expr::new(RawExpr::NatLiteral(1)),
        )));
    }

    #[test]
    fn nested_sequence_binders_shift_without_capture() {
        let outer = Variable::new("i");
        let inner = TypeExpr::Seq(
            Expr::new(RawExpr::Type(TypeExpr::Matrix(
                Expr::new(RawExpr::Variable(outer.clone())),
                Expr::new(RawExpr::BoundNatural(0)),
            ))),
            Expr::new(RawExpr::NatLiteral(2)),
        );
        let abstracted =
            abstract_type_variable(&inner, &outer, &Expr::new(RawExpr::BoundNatural(0)));
        assert!(!contains_unbound_natural(&TypeExpr::Seq(
            Expr::new(RawExpr::Type(abstracted)),
            Expr::new(RawExpr::NatLiteral(3)),
        )));
    }
}
