//! Datatype-only fragments for bounded proof DAGs with canonical BFS slots. These helpers build
//! constraints but do not assert them, invoke a solver, or establish premises.
use super::{
    Error, ExprDatatype,
    schema::{app, field, tag},
};
use crate::Finop;
use z3::{
    DatatypeAccessor, DatatypeBuilder, DatatypeSort, Symbol,
    ast::{Ast, Bool, Datatype, Dynamic},
    datatype_builder::create_datatypes,
};

/// Immediate selector edges, guarded by the constructor owning each selector.
/// A missing result-sort match is false; an unregistered parent sort is an error.
pub fn selector_child(
    datatypes: &[&DatatypeSort],
    parent: &Dynamic,
    child: &Dynamic,
) -> Result<Bool, Error> {
    let sort = datatypes
        .iter()
        .find(|s| s.sort == parent.get_sort())
        .ok_or(Error::UnregisteredDatatype)?;
    let mut cases = Vec::new();
    for variant in &sort.variants {
        let guard = variant.tester.apply(&[parent]).as_bool().unwrap();
        for selector in &variant.accessors {
            let selected = selector.apply(&[parent]);
            if selected.get_sort() == child.get_sort() {
                cases.push(Bool::and(&[guard.clone(), selected.eq(child)]));
            }
        }
    }
    Ok(Bool::or(&cases))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofRule {
    AndIntroduction,
    ImplicationIntroduction,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssumptionRef {
    Ambient(u64),
    Temporary(u64),
}

/// One evaluated constructor layer; children remain SMT values.
#[derive(Clone, Debug)]
pub enum ProofNode {
    Unused,
    Assumption {
        conclusion: Datatype,
        source: AssumptionRef,
    },
    Established {
        conclusion: Datatype,
        source: u64,
    },
    Inference {
        conclusion: Datatype,
        rule: ProofRule,
        premises: Datatype,
    },
}

/// Pure Boolean sequential threshold counter, retaining QF_DT.
pub fn at_most(bits: &[Bool], bound: usize) -> Bool {
    if bound >= bits.len() {
        return Bool::from_bool(true);
    }
    if bound == 0 {
        return Bool::and(&bits.iter().map(Bool::not).collect::<Vec<_>>());
    }
    let mut thresholds = vec![Bool::from_bool(false); bound + 2];
    thresholds[0] = Bool::from_bool(true);
    let mut constraints = Vec::new();
    for bit in bits {
        let mut next = vec![Bool::from_bool(true)];
        for k in 1..thresholds.len() {
            let value = Bool::fresh_const("dependency_threshold");
            constraints.push(value.eq(Bool::or(&[
                thresholds[k].clone(),
                Bool::and(&[bit.clone(), thresholds[k - 1].clone()]),
            ])));
            next.push(value);
        }
        thresholds = next;
    }
    constraints.push(thresholds[bound + 1].not());
    Bool::and(&constraints)
}

struct PremisePosition {
    present: Bool,
    child: Datatype,
    last: Bool,
}

pub struct ProofDatatype {
    proof: DatatypeSort,
    list: DatatypeSort,
    rule: DatatypeSort,
    expression: z3::Sort,
    assumption: DatatypeSort,
}
impl ProofDatatype {
    pub fn new(namespace: &str, expressions: &ExprDatatype) -> Self {
        let proof_name = format!("{namespace}.Proof");
        let list_name = format!("{namespace}.ProofList");
        let rule_name = format!("{namespace}.ProofRule");
        let assumption_name = format!("{namespace}.AssumptionRef");
        let mut sorts = create_datatypes(vec![
            DatatypeBuilder::new(proof_name.clone())
                .variant(&format!("{namespace}.Unused"), vec![])
                .variant(
                    &format!("{namespace}.Assumption"),
                    vec![
                        (
                            &format!("{namespace}.Assumption_conclusion"),
                            DatatypeAccessor::sort(expressions.sort().sort.clone()),
                        ),
                        (
                            &format!("{namespace}.Assumption_source"),
                            DatatypeAccessor::datatype(assumption_name.clone()),
                        ),
                    ],
                )
                .variant(
                    &format!("{namespace}.Established"),
                    vec![
                        (
                            &format!("{namespace}.Established_conclusion"),
                            DatatypeAccessor::sort(expressions.sort().sort.clone()),
                        ),
                        (
                            &format!("{namespace}.Established_source"),
                            DatatypeAccessor::sort(expressions.schema.natural.sort.clone()),
                        ),
                    ],
                )
                .variant(
                    &format!("{namespace}.Inference"),
                    vec![
                        (
                            &format!("{namespace}.Inference_conclusion"),
                            DatatypeAccessor::sort(expressions.sort().sort.clone()),
                        ),
                        (
                            &format!("{namespace}.Inference_rule"),
                            DatatypeAccessor::datatype(rule_name.clone()),
                        ),
                        (
                            &format!("{namespace}.Inference_premises"),
                            DatatypeAccessor::datatype(list_name.clone()),
                        ),
                    ],
                ),
            DatatypeBuilder::new(list_name)
                .variant(&format!("{namespace}.Nil"), vec![])
                .variant(
                    &format!("{namespace}.Cons"),
                    vec![
                        (
                            &format!("{namespace}.Cons_head"),
                            DatatypeAccessor::datatype(proof_name),
                        ),
                        (
                            &format!("{namespace}.Cons_tail"),
                            DatatypeAccessor::datatype(format!("{namespace}.ProofList")),
                        ),
                    ],
                ),
            DatatypeBuilder::new(rule_name)
                .variant(&format!("{namespace}.AndIntroduction"), vec![])
                .variant(&format!("{namespace}.ImplicationIntroduction"), vec![]),
            DatatypeBuilder::new(assumption_name)
                .variant(
                    &format!("{namespace}.Ambient"),
                    vec![(
                        &format!("{namespace}.Ambient_index"),
                        DatatypeAccessor::sort(expressions.schema.natural.sort.clone()),
                    )],
                )
                .variant(
                    &format!("{namespace}.Temporary"),
                    vec![(
                        &format!("{namespace}.Temporary_index"),
                        DatatypeAccessor::sort(expressions.schema.natural.sort.clone()),
                    )],
                ),
        ])
        .into_iter();
        Self {
            proof: sorts.next().unwrap(),
            list: sorts.next().unwrap(),
            rule: sorts.next().unwrap(),
            assumption: sorts.next().unwrap(),
            expression: expressions.sort().sort.clone(),
        }
    }
    pub fn sort(&self) -> &DatatypeSort {
        &self.proof
    }
    pub fn datatypes(&self) -> [&DatatypeSort; 4] {
        [&self.proof, &self.list, &self.rule, &self.assumption]
    }
    pub fn constant(&self, name: impl Into<Symbol>) -> Datatype {
        Datatype::new_const(name, &self.proof.sort)
    }
    fn check(&self, node: &Datatype) -> Result<(), Error> {
        if node.get_sort() == self.proof.sort {
            Ok(())
        } else {
            Err(Error::WrongSort)
        }
    }
    fn tester(&self, node: &Datatype, variant: usize) -> Result<Bool, Error> {
        self.check(node)?;
        Ok(self.proof.variants[variant]
            .tester
            .apply(&[node])
            .as_bool()
            .unwrap())
    }
    pub fn is_unused(&self, node: &Datatype) -> Result<Bool, Error> {
        self.tester(node, 0)
    }
    pub fn is_leaf(&self, node: &Datatype) -> Result<Bool, Error> {
        Ok(Bool::or(&[self.tester(node, 1)?, self.tester(node, 2)?]))
    }
    pub fn is_inference(&self, node: &Datatype) -> Result<Bool, Error> {
        self.tester(node, 3)
    }
    pub fn unused(&self) -> Datatype {
        app(&self.proof, "Unused", &[])
    }
    pub fn assumption(
        &self,
        conclusion: &Datatype,
        source: AssumptionRef,
        expressions: &ExprDatatype,
    ) -> Result<Datatype, Error> {
        self.check_expression(conclusion, expressions)?;
        let (name, index) = match source {
            AssumptionRef::Ambient(i) => ("Ambient", i),
            AssumptionRef::Temporary(i) => ("Temporary", i),
        };
        let reference = app(&self.assumption, name, &[expressions.natural(index)]);
        Ok(app(
            &self.proof,
            "Assumption",
            &[conclusion.clone(), reference],
        ))
    }
    pub fn established(
        &self,
        conclusion: &Datatype,
        source: u64,
        expressions: &ExprDatatype,
    ) -> Result<Datatype, Error> {
        self.check_expression(conclusion, expressions)?;
        Ok(app(
            &self.proof,
            "Established",
            &[conclusion.clone(), expressions.natural(source)],
        ))
    }
    fn check_expression(&self, value: &Datatype, expressions: &ExprDatatype) -> Result<(), Error> {
        if value.get_sort() == self.expression && expressions.sort().sort == self.expression {
            Ok(())
        } else {
            Err(Error::WrongSort)
        }
    }
    pub fn inference(
        &self,
        conclusion: &Datatype,
        rule: ProofRule,
        premises: &[Datatype],
    ) -> Result<Datatype, Error> {
        if conclusion.get_sort() != self.expression {
            return Err(Error::WrongSort);
        }
        let mut list = app(&self.list, "Nil", &[]);
        for premise in premises.iter().rev() {
            self.check(premise)?;
            list = app(&self.list, "Cons", &[premise.clone(), list]);
        }
        let rule = match rule {
            ProofRule::AndIntroduction => app(&self.rule, "AndIntroduction", &[]),
            ProofRule::ImplicationIntroduction => app(&self.rule, "ImplicationIntroduction", &[]),
        };
        Ok(app(
            &self.proof,
            "Inference",
            &[conclusion.clone(), rule, list],
        ))
    }
    /// Symbolic conclusion selector. Callers must constrain the node not to be
    /// Unused; selectors on inapplicable constructors otherwise have no meaning.
    pub fn conclusion(&self, node: &Datatype) -> Result<Datatype, Error> {
        self.check(node)?;
        let select = |variant: usize| {
            self.proof.variants[variant].accessors[0]
                .apply(&[node])
                .as_datatype()
                .unwrap()
        };
        Ok(self.tester(node, 1)?.ite(
            &select(1),
            &self.tester(node, 2)?.ite(&select(2), &select(3)),
        ))
    }
    pub fn inspect(
        &self,
        value: &Datatype,
        expressions: &ExprDatatype,
    ) -> Result<ProofNode, Error> {
        if expressions.sort().sort != self.expression {
            return Err(Error::WrongSort);
        }
        match tag(value, &self.proof)?.as_str() {
            "Unused" => Ok(ProofNode::Unused),
            "Assumption" => {
                let reference = field(value, 1)?;
                let index = expressions.read_natural(&field(&reference, 0)?)?;
                let source = match tag(&reference, &self.assumption)?.as_str() {
                    "Ambient" => AssumptionRef::Ambient(index),
                    "Temporary" => AssumptionRef::Temporary(index),
                    _ => return Err(Error::Malformed("unknown assumption reference")),
                };
                Ok(ProofNode::Assumption {
                    conclusion: field(value, 0)?,
                    source,
                })
            }
            "Established" => Ok(ProofNode::Established {
                conclusion: field(value, 0)?,
                source: expressions.read_natural(&field(value, 1)?)?,
            }),
            "Inference" => {
                let rule = match tag(&field(value, 1)?, &self.rule)?.as_str() {
                    "AndIntroduction" => ProofRule::AndIntroduction,
                    "ImplicationIntroduction" => ProofRule::ImplicationIntroduction,
                    _ => return Err(Error::Malformed("unknown proof rule")),
                };
                Ok(ProofNode::Inference {
                    conclusion: field(value, 0)?,
                    rule,
                    premises: field(value, 2)?,
                })
            }
            _ => Err(Error::Malformed("unknown proof constructor")),
        }
    }
    /// Inspect an evaluated premise list without allowing an unbounded tail.
    pub fn read_premises(&self, value: &Datatype, capacity: usize) -> Result<Vec<Datatype>, Error> {
        let mut tail = value.clone();
        let mut result = Vec::new();
        loop {
            match tag(&tail, &self.list)?.as_str() {
                "Nil" => return Ok(result),
                "Cons" if result.len() < capacity => {
                    result.push(field(&tail, 0)?);
                    tail = field(&tail, 1)?;
                }
                "Cons" => return Err(Error::Malformed("proof premise capacity exceeded")),
                _ => return Err(Error::Malformed("unknown premise-list constructor")),
            }
        }
    }
    /// One local rule application; does not check how the premises were proved.
    pub fn and_introduction(
        &self,
        expressions: &ExprDatatype,
        premises: &[Datatype],
        parent: &Datatype,
    ) -> Result<Bool, Error> {
        self.check(parent)?;
        if expressions.sort().sort != self.expression {
            return Err(Error::WrongSort);
        }
        if premises.is_empty() {
            return Err(Error::Malformed(
                "conjunction introduction requires premises",
            ));
        }
        let mut guards = Vec::new();
        let mut conclusions = Vec::new();
        for p in premises {
            guards.push(self.is_unused(p)?.not());
            conclusions.push(self.conclusion(p)?);
        }
        let conclusion = expressions.finite(Finop::And, &conclusions)?;
        guards.push(parent.eq(self.inference(
            &conclusion,
            ProofRule::AndIntroduction,
            premises,
        )?));
        Ok(Bool::and(&guards))
    }
    pub fn implication_introduction(
        &self,
        expressions: &ExprDatatype,
        premise: &Datatype,
        parent: &Datatype,
    ) -> Result<Bool, Error> {
        self.check(parent)?;
        let antecedent = expressions.antecedent(&self.conclusion(parent)?)?;
        let formula = expressions.implication(&antecedent, &self.conclusion(premise)?)?;
        Ok(Bool::and(&[
            self.is_unused(premise)?.not(),
            parent.eq(self.inference(
                &formula,
                ProofRule::ImplicationIntroduction,
                std::slice::from_ref(premise),
            )?),
        ]))
    }
    /// Unroll semantic proof-premise positions once, guarding every list selector.
    /// `last` also checks termination, so a tail cannot hide additional children.
    fn premise_positions(
        &self,
        node: &Datatype,
        capacity: usize,
    ) -> Result<Vec<PremisePosition>, Error> {
        self.check(node)?;
        let mut tail = self.proof.variants[3].accessors[2]
            .apply(&[node])
            .as_datatype()
            .unwrap();
        let mut present = self.is_inference(node)?;
        let mut positions = Vec::new();
        for _ in 0..capacity {
            present = Bool::and(&[
                present,
                self.list.variants[1]
                    .tester
                    .apply(&[&tail])
                    .as_bool()
                    .unwrap(),
            ]);
            let child = self.list.variants[1].accessors[0]
                .apply(&[&tail])
                .as_datatype()
                .unwrap();
            tail = self.list.variants[1].accessors[1]
                .apply(&[&tail])
                .as_datatype()
                .unwrap();
            let last = Bool::and(&[
                present.clone(),
                self.list.variants[0]
                    .tester
                    .apply(&[&tail])
                    .as_bool()
                    .unwrap(),
            ]);
            positions.push(PremisePosition {
                present: present.clone(),
                child,
                last,
            });
        }
        Ok(positions)
    }
    /// Guarded, exactly terminated list cases of lengths 1..=capacity.
    pub(crate) fn premise_cases(
        &self,
        node: &Datatype,
        capacity: usize,
    ) -> Result<Vec<(Bool, Vec<Datatype>)>, Error> {
        let mut heads = Vec::new();
        Ok(self
            .premise_positions(node, capacity)?
            .into_iter()
            .map(|position| {
                heads.push(position.child);
                (position.last, heads.clone())
            })
            .collect())
    }
    /// Canonical BFS numbering of distinct reachable non-leaf proof values.
    /// Leaves consume no slots; repeated edges share one slot. See
    /// docs/symmetry-breaking.md for the discovery and coverage constraints.
    pub fn bounded_structure(
        &self,
        root: &Datatype,
        slots: &[Datatype],
        contextual_leaves: &[Datatype],
        max_premises: usize,
    ) -> Result<Bool, Error> {
        self.check(root)?;
        let mut constraints = contextual_leaves
            .iter()
            .map(|p| self.is_leaf(p))
            .collect::<Result<Vec<_>, _>>()?;
        let leaf_member = |p: &Datatype| {
            Bool::or(
                &contextual_leaves
                    .iter()
                    .map(|leaf| p.eq(leaf))
                    .collect::<Vec<_>>(),
            )
        };
        if slots.is_empty() {
            constraints.push(leaf_member(root));
            return Ok(Bool::and(&constraints));
        }
        let active = slots
            .iter()
            .map(|s| self.is_unused(s).map(|unused| unused.not()))
            .collect::<Result<Vec<_>, _>>()?;
        constraints.push(Bool::or(&[leaf_member(root), self.is_inference(root)?]));
        constraints.push(self.is_inference(root)?.eq(&active[0]));
        constraints.push(active[0].implies(root.eq(&slots[0])));
        for (i, slot) in slots.iter().enumerate() {
            constraints.push(active[i].implies(self.is_inference(slot)?));
            if i > 0 {
                constraints.push(active[i].implies(&active[i - 1]));
            }
            for j in 0..i {
                constraints.push(
                    Bool::and(&[active[i].clone(), active[j].clone()])
                        .implies(slot.eq(&slots[j]).not()),
                );
            }
        }
        // D at each position means "discovered strictly before this position".
        // Fresh names isolate separate fragments even when they share a codec.
        let mut before = (0..slots.len())
            .map(|j| Bool::from_bool(j == 0))
            .collect::<Vec<_>>();
        for (i, slot) in slots.iter().enumerate() {
            let positions = self.premise_positions(slot, max_premises)?;
            constraints.push(active[i].implies(Bool::or(
                &positions.iter().map(|p| p.last.clone()).collect::<Vec<_>>(),
            )));
            for (ell, position) in positions.into_iter().enumerate() {
                let discovered = (0..slots.len())
                    .map(|_| Bool::fresh_const("proof_discovered"))
                    .collect::<Vec<_>>();
                let edges = (0..slots.len())
                    .map(|_| Bool::fresh_const("proof_edge"))
                    .collect::<Vec<_>>();
                for j in 0..slots.len() {
                    constraints.push(discovered[j].eq(&before[j]));
                    constraints.push(edges[j].eq(Bool::and(&[
                        position.present.clone(),
                        active[j].clone(),
                        position.child.eq(&slots[j]),
                    ])));
                    if j > 0 {
                        constraints.push(edges[j].implies(&discovered[j - 1]));
                    }
                }
                if ell == 0 && i > 0 {
                    constraints.push(active[i].implies(&discovered[i]));
                }
                let internal = self.is_inference(&position.child)?;
                constraints.push(
                    position
                        .present
                        .implies(Bool::or(&[leaf_member(&position.child), internal.clone()])),
                );
                constraints
                    .push(Bool::and(&[position.present, internal]).implies(Bool::or(&edges)));
                before = discovered
                    .into_iter()
                    .zip(edges)
                    .map(|(d, e)| Bool::or(&[d, e]))
                    .collect();
            }
        }
        Ok(Bool::and(&constraints))
    }
    /// Rule-policy disjunction, independent of the ordering constraints.
    pub fn rule_constraints(
        &self,
        expressions: &ExprDatatype,
        slots: &[Datatype],
        max_premises: usize,
    ) -> Result<Bool, Error> {
        let mut constraints = Vec::new();
        for slot in slots {
            let mut rules = Vec::new();
            for (shape, premises) in self.premise_cases(slot, max_premises)? {
                let mut applications = vec![self.and_introduction(expressions, &premises, slot)?];
                if premises.len() == 1 {
                    applications.push(self.implication_introduction(
                        expressions,
                        &premises[0],
                        slot,
                    )?);
                }
                rules.push(Bool::and(&[shape, Bool::or(&applications)]));
            }
            constraints.push(self.is_inference(slot)?.implies(Bool::or(&rules)));
        }
        Ok(Bool::and(&constraints))
    }
}
