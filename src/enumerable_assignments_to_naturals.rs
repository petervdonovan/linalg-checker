use std::collections::HashMap;

use crate::{
    Variable,
    enumerable_assignments_to_naturals::equivalence_classes::{
        EquivalenceClassId, EquivalenceClasses, NodeId,
    },
};

mod equivalence_classes {
    use crate::Variable;

    #[derive(Clone, Copy)]
    pub struct NodeId(u32);

    #[derive(Clone, Copy)]
    pub struct EquivalenceClassId(NodeId);

    pub struct Node {
        parent: Option<NodeId>,
        rank: u32,
        variable: Variable,
    }
    #[derive(Default)]
    pub struct EquivalenceClasses {
        nodes: Vec<Node>,
    }
    impl EquivalenceClasses {
        fn add_node(&mut self, variable: Variable) {}
        fn unify(&mut self, node0: NodeId, node1: NodeId) {}
    }
}

enum LtRelation {
    Lt,
    LtOrEqual,
}

pub struct NaturalsWithComparisonAndEquality {
    classes: EquivalenceClasses,
    class_to_smaller_classes: HashMap<EquivalenceClassId, Vec<(LtRelation, EquivalenceClassId)>>,
    // create the topological sort by bfs, where we always pop the alphabetically latest element from the frontier
    topological_sort_least_to_greatest: Vec<EquivalenceClassId>,
    computed_classes: HashMap<EquivalenceClassId, Box<dyn Fn(Assignment<'_>) -> u64>>,
    node_lower_bound_inclusive: HashMap<EquivalenceClassId, u64>,
    node_upper_bound_inclusive: HashMap<EquivalenceClassId, u64>,
}
#[derive(Default)]
pub struct NaturalsWithComparisonAndEqualityBuilder {
    classes: EquivalenceClasses,
    variable_to_node_id: HashMap<Variable, NodeId>,
    lt_relations: Vec<(NodeId, LtRelation, NodeId)>,
    computed_nodes: HashMap<NodeId, Box<dyn Fn(Assignment<'_>) -> u64>>,
    node_lower_bound_inclusive: HashMap<NodeId, u64>,
    node_upper_bound_inclusive: HashMap<NodeId, u64>,
}

impl NaturalsWithComparisonAndEqualityBuilder {
    fn build(self) -> NaturalsWithComparisonAndEquality {
        todo!()
    }
    fn intern_var(&mut self, v: Variable) -> NodeId {
        todo!()
    }
    fn mark_node_as_computed_from_other_nodes(
        &mut self,
        v: NodeId,
        f: Box<dyn Fn(Assignment<'_>) -> u64>,
    ) {
    }
    fn push_eq(&mut self, v0: NodeId, v1: NodeId) {
        todo!()
    }
    fn push_inequality(&mut self, v0: NodeId, lt: LtRelation, v1: NodeId) {
        todo!()
    }
}

pub struct AssignmentIterator<'a> {
    constraints: &'a NaturalsWithComparisonAndEquality,
    next_assignment_to_topologically_sorted_classes: Vec<u64>,
}

pub struct Assignment<'a> {
    constraints: &'a NaturalsWithComparisonAndEquality,
    values: Vec<u64>,
}

impl NaturalsWithComparisonAndEquality {
    pub fn assignments(&self) -> AssignmentIterator<'_> {
        todo!()
    }
}

impl<'a> Iterator for AssignmentIterator<'a> {
    type Item = Assignment<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!(
            "iterate in increasing order of the sum of the values assigned to the equivalence classes, breaking ties deterministically"
        )
    }
}

impl Assignment<'_> {
    pub fn get_value(v: &Variable) -> u64 {
        todo!()
    }
}
