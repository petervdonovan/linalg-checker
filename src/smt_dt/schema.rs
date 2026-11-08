use super::Error;
use crate::{Binop, Cmp, Finop, Monop, SeqOp};
use z3::{
    DatatypeAccessor, DatatypeBuilder, DatatypeSort,
    ast::{Ast, Datatype},
    datatype_builder::create_datatypes,
};

pub(super) const MONOPS: &[(Monop, &str)] = &[
    (Monop::Neg, "Neg"),
    (Monop::Not, "Not"),
    (Monop::Transpose, "Transpose"),
    (Monop::Diag, "Diag"),
    (Monop::Trace, "Trace"),
    (Monop::Det, "Det"),
];
pub(super) const BINOPS: &[(Binop, &str)] = &[
    (Binop::Div, "Div"),
    (Binop::Power, "Power"),
    (Binop::Cast, "Cast"),
    (Binop::ElementOf, "ElementOf"),
    (Binop::InDomain, "InDomain"),
    (Binop::SingleSubscript, "SingleSubscript"),
];
pub(super) const FINOPS: &[(Finop, &str)] = &[
    (Finop::Plus, "Plus"),
    (Finop::Times, "Times"),
    (Finop::And, "And"),
    (Finop::Or, "Or"),
];
pub(super) const QUANTIFIERS: &[(Finop, &str)] =
    &[(Finop::Forall, "Forall"), (Finop::Exists, "Exists")];
pub(super) const COMPARISONS: &[(Cmp, &str)] = &[
    (Cmp::Eq, "Eq"),
    (Cmp::Ne, "Ne"),
    (Cmp::Lt, "Lt"),
    (Cmp::Gt, "Gt"),
    (Cmp::Le, "Le"),
    (Cmp::Ge, "Ge"),
];
pub(super) const SEQOPS: &[(SeqOp, &str)] = &[
    (SeqOp::Sum, "Sum"),
    (SeqOp::Prod, "Prod"),
    (SeqOp::BigOr, "BigOr"),
    (SeqOp::Map, "Map"),
];

pub(super) struct EnumSort<T: 'static> {
    pub sort: DatatypeSort,
    pub values: &'static [(T, &'static str)],
}
impl<T: Copy + Eq> EnumSort<T> {
    pub fn encode(&self, value: T) -> Result<Datatype, Error> {
        let i = self
            .values
            .iter()
            .position(|(v, _)| *v == value)
            .ok_or(Error::Unsupported("operator"))?;
        Ok(self.sort.variants[i]
            .constructor
            .apply(&[])
            .as_datatype()
            .unwrap())
    }
    pub fn decode(&self, value: &Datatype) -> Result<T, Error> {
        let i = variant(value, &self.sort)?;
        Ok(self.values[i].0)
    }
}

// DatatypeAccessor references resolve inside this mutually recursive group.
fn builder(ns: &str, sort: &str, variants: &[(&str, &[(&str, &str)])]) -> DatatypeBuilder {
    let mut result = DatatypeBuilder::new(format!("{ns}.{sort}"));
    for (name, fields) in variants {
        let labels = fields
            .iter()
            .map(|(label, _)| format!("{ns}.{name}_{label}"))
            .collect::<Vec<_>>();
        let fields = fields
            .iter()
            .zip(&labels)
            .map(|((_, sort), label)| {
                let accessor = if *sort == "Bool" {
                    DatatypeAccessor::sort(z3::Sort::bool())
                } else {
                    DatatypeAccessor::datatype(format!("{ns}.{sort}"))
                };
                (label.as_str(), accessor)
            })
            .collect();
        result = result.variant(&format!("{ns}.{name}"), fields);
    }
    result
}
fn enumeration<T>(ns: &str, name: &str, values: &[(T, &str)]) -> DatatypeBuilder {
    let mut result = DatatypeBuilder::new(format!("{ns}.{name}"));
    for (_, value) in values {
        result = result.variant(&format!("{ns}.{name}{value}"), vec![]);
    }
    result
}

pub(super) struct Schema {
    pub natural: DatatypeSort,
    pub positive: DatatypeSort,
    pub monop: EnumSort<Monop>,
    pub binop: EnumSort<Binop>,
    pub finop: EnumSort<Finop>,
    pub quantifier: EnumSort<Finop>,
    pub comparison: EnumSort<Cmp>,
    pub seqop: EnumSort<SeqOp>,
    pub expr: DatatypeSort,
    pub ty: DatatypeSort,
    pub list: DatatypeSort,
    pub finite_lists: Vec<DatatypeSort>,
}
impl Schema {
    pub fn new(ns: &str, max_finop_arity: Option<usize>) -> Self {
        let finite_list = max_finop_arity
            .map(|k| format!("FinopArgs{k}"))
            .unwrap_or_else(|| "ExprList".into());
        let mut definitions = vec![
            builder(
                ns,
                "Natural",
                &[("NZero", &[]), ("NPositive", &[("value", "Positive")])],
            ),
            builder(
                ns,
                "Positive",
                &[
                    ("POne", &[]),
                    ("PDouble", &[("half", "Positive")]),
                    ("PDoublePlusOne", &[("half", "Positive")]),
                ],
            ),
            enumeration(ns, "Monop", MONOPS),
            enumeration(ns, "Binop", BINOPS),
            enumeration(ns, "Finop", FINOPS),
            enumeration(ns, "Quantifier", QUANTIFIERS),
            enumeration(ns, "Comparison", COMPARISONS),
            enumeration(ns, "SeqOp", SEQOPS),
            builder(
                ns,
                "Expr",
                &[
                    ("Var", &[("id", "Natural")]),
                    ("NatLiteral", &[("value", "Natural")]),
                    ("BoolLiteral", &[("value", "Bool")]),
                    ("TypeValue", &[("value", "Type")]),
                    ("Implicit", &[("id", "Natural")]),
                    ("Bound", &[("index", "Natural")]),
                    ("Identity", &[("dimension", "Natural")]),
                    ("Zero", &[("rows", "Natural"), ("cols", "Natural")]),
                    ("Basis", &[("index", "Expr"), ("dimension", "Natural")]),
                    (
                        "MatrixLiteral",
                        &[
                            ("rows", "Natural"),
                            ("cols", "Natural"),
                            ("cells", "ExprList"),
                        ],
                    ),
                    ("Unary", &[("operator", "Monop"), ("operand", "Expr")]),
                    (
                        "Binary",
                        &[("operator", "Binop"), ("left", "Expr"), ("right", "Expr")],
                    ),
                    (
                        "Finite",
                        &[("operator", "Finop"), ("arguments", &finite_list)],
                    ),
                    (
                        "Compare",
                        &[
                            ("operator", "Comparison"),
                            ("left", "Expr"),
                            ("right", "Expr"),
                        ],
                    ),
                    ("Implies", &[("left", "Expr"), ("right", "Expr")]),
                    (
                        "Quantified",
                        &[
                            ("operator", "Quantifier"),
                            ("premises", "ExprList"),
                            ("body", "Expr"),
                        ],
                    ),
                    ("SequenceLiteral", &[("elements", "ExprList")]),
                    (
                        "SequenceOp",
                        &[
                            ("operator", "SeqOp"),
                            ("binder", "Natural"),
                            ("from", "Expr"),
                            ("to", "Expr"),
                            ("body", "Expr"),
                        ],
                    ),
                    (
                        "Comprehension",
                        &[
                            ("binder", "Natural"),
                            ("domain", "Type"),
                            ("predicate", "Expr"),
                        ],
                    ),
                    ("EmptySet", &[]),
                ],
            ),
            builder(
                ns,
                "Type",
                &[
                    ("BoolType", &[]),
                    ("NatType", &[]),
                    ("IntType", &[]),
                    ("RealType", &[]),
                    ("SetType", &[("element", "Type")]),
                    ("MatrixType", &[("rows", "Expr"), ("cols", "Expr")]),
                    ("SequenceType", &[("element", "Expr"), ("length", "Expr")]),
                ],
            ),
            builder(
                ns,
                "ExprList",
                &[
                    ("ExprNil", &[]),
                    ("ExprCons", &[("head", "Expr"), ("tail", "ExprList")]),
                ],
            ),
        ];
        if let Some(max) = max_finop_arity {
            for capacity in 0..=max {
                let sort = format!("FinopArgs{capacity}");
                let nil = format!("FinopNil{capacity}");
                let cons = format!("FinopCons{capacity}");
                let previous = format!("FinopArgs{}", capacity.saturating_sub(1));
                let mut variants = vec![(nil.as_str(), &[][..])];
                let fields = [("head", "Expr"), ("tail", previous.as_str())];
                if capacity > 0 {
                    variants.push((cons.as_str(), &fields));
                }
                definitions.push(builder(ns, &sort, &variants));
            }
        }
        let mut sorts = create_datatypes(definitions).into_iter();
        Self {
            natural: sorts.next().unwrap(),
            positive: sorts.next().unwrap(),
            monop: EnumSort {
                sort: sorts.next().unwrap(),
                values: MONOPS,
            },
            binop: EnumSort {
                sort: sorts.next().unwrap(),
                values: BINOPS,
            },
            finop: EnumSort {
                sort: sorts.next().unwrap(),
                values: FINOPS,
            },
            quantifier: EnumSort {
                sort: sorts.next().unwrap(),
                values: QUANTIFIERS,
            },
            comparison: EnumSort {
                sort: sorts.next().unwrap(),
                values: COMPARISONS,
            },
            seqop: EnumSort {
                sort: sorts.next().unwrap(),
                values: SEQOPS,
            },
            expr: sorts.next().unwrap(),
            ty: sorts.next().unwrap(),
            list: sorts.next().unwrap(),
            finite_lists: sorts.collect(),
        }
    }
    pub fn natural(&self, n: u64) -> Datatype {
        if n == 0 {
            app(&self.natural, "NZero", &[])
        } else {
            app(&self.natural, "NPositive", &[self.positive(n)])
        }
    }
    fn positive(&self, n: u64) -> Datatype {
        if n == 1 {
            app(&self.positive, "POne", &[])
        } else {
            app(
                &self.positive,
                if n.is_multiple_of(2) {
                    "PDouble"
                } else {
                    "PDoublePlusOne"
                },
                &[self.positive(n / 2)],
            )
        }
    }
    pub fn read_natural(&self, value: &Datatype) -> Result<u64, Error> {
        match tag(value, &self.natural)?.as_str() {
            "NZero" => Ok(0),
            "NPositive" => self.read_positive(&field(value, 0)?),
            _ => unreachable!(),
        }
    }
    fn read_positive(&self, value: &Datatype) -> Result<u64, Error> {
        match tag(value, &self.positive)?.as_str() {
            "POne" => Ok(1),
            kind => {
                let half = self.read_positive(&field(value, 0)?)?;
                half.checked_mul(2)
                    .and_then(|n| n.checked_add(u64::from(kind == "PDoublePlusOne")))
                    .ok_or(Error::NumericOverflow)
            }
        }
    }
}

pub(super) fn app(sort: &DatatypeSort, name: &str, fields: &[Datatype]) -> Datatype {
    let variant = sort
        .variants
        .iter()
        .find(|v| v.constructor.name().rsplit('.').next() == Some(name))
        .expect("constructor belongs to schema");
    let fields = fields.iter().map(|v| v as &dyn Ast).collect::<Vec<_>>();
    variant.constructor.apply(&fields).as_datatype().unwrap()
}
fn variant(value: &Datatype, sort: &DatatypeSort) -> Result<usize, Error> {
    if value.get_sort() != sort.sort {
        return Err(Error::WrongSort);
    }
    let declaration = value.safe_decl().map_err(|_| Error::UnevaluatedTerm)?;
    if declaration.kind() != z3::DeclKind::DtConstructor {
        return Err(Error::UnevaluatedTerm);
    }
    sort.variants
        .iter()
        .position(|v| v.constructor.name() == declaration.name())
        .ok_or(Error::Malformed("unknown constructor"))
}
pub(super) fn tag(value: &Datatype, sort: &DatatypeSort) -> Result<String, Error> {
    let index = variant(value, sort)?;
    Ok(sort.variants[index]
        .constructor
        .name()
        .rsplit('.')
        .next()
        .unwrap()
        .to_owned())
}
pub(super) fn field(value: &Datatype, index: usize) -> Result<Datatype, Error> {
    value
        .nth_child(index)
        .and_then(|v| v.as_datatype())
        .ok_or(Error::Malformed("expected datatype field"))
}
