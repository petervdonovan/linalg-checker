# Symmetry Breaking for Bounded Proof DAGs Using BFS Slot Assignment

## 1. Objective

This document specifies a symmetry-breaking encoding for representing a bounded proof DAG in quantifier-free SMT using a finite collection of symbolic slots.

The goal is to eliminate redundant assignments of DAG nodes to slots. Without symmetry breaking, a proof DAG with \(m\) distinct non-leaf nodes may admit up to \(m!\) assignments to \(m\) slots, all representing the same proof.

We impose a **canonical breadth-first ordering** on the slots, using the order of children within each node.

The encoding:

- Supports rooted directed acyclic graphs (DAGs), including shared subproofs.
- Supports nodes with 0, 1, 2, or 3 ordered children.
- Assigns slots only to non-leaf nodes.
- Allows unused slots, represented by `null`.
- Does not introduce node identifiers as fields of the proof datatype.
- Does not compare constructors, formulas, or other data stored in nodes to determine their ordering.
- Does not enumerate possible DAG topologies.
- Requires no custom SMT solver modifications.
- Uses \(O(n^2)\) constraints and auxiliary Boolean variables for a fixed maximum child arity.

The encoding is intended to be combined with separate constraints expressing the validity of inference rules and the desired proof conclusion.

## 2. Assumptions and notation

Let:

- \(n\) be the maximum number of non-leaf proof nodes.
- \(a\) be the maximum child arity, with \(a=3\) in the intended application.
- \(r\) be the root of the proof DAG.
- \(s_0,\ldots,s_{n-1}\) be symbolic constants of the proof-node datatype.
- `null` be a distinguished value representing an unused slot.

Each slot \(s_i\) contains either:

1. A non-leaf proof node, or
2. `null`.

Leaves do not occupy slots.

The proof-node datatype must distinguish valid proof nodes from `null`. If `null` is introduced as a datatype constructor, it must not be permitted as a child of a valid proof node.

The child positions of a node are ordered. For example, a node may have children

\[
[u,v,w],
\]

where \(u\), \(v\), and \(w\) are its first, second, and third children.

Repeated references are permitted:

\[
[u,v,u]
\]

is a valid child list.

We assume that proof nodes are represented by an inductive algebraic datatype, so cyclic constructor structures are excluded by the datatype semantics.

### 2.1 Non-leaf predicate

Define

\[
\operatorname{NonLeaf}(v)
\]

to mean that \(v\) is a valid proof node with at least one child.

For a proof datatype with fixed-arity constructors, this predicate can be implemented as a disjunction of constructor testers.

In particular,

\[
\operatorname{NonLeaf}(\texttt{null})=\bot.
\]

### 2.2 Child positions

A **child position** is a pair

\[
(i,\ell),
\]

where:

- \(i\in\{0,\ldots,n-1\}\) identifies the parent slot \(s_i\).
- \(\ell\in\{0,\ldots,a-1\}\) identifies a potential child position within that parent.

The child positions are ordered lexicographically:

\[
(0,0),(0,1),\ldots,(0,a-1),
(1,0),\ldots,(n-1,a-1).
\]

A child position is *present* only if \(s_i\) is active and its constructor has at least \(\ell+1\) children.

Define

\[
P_{i,\ell}
\iff
s_i\ne\texttt{null}
\land
\operatorname{arity}(s_i)>\ell.
\]

For a present child position, let

\[
C_{i,\ell}
\]

denote the corresponding child.

The value \(C_{i,\ell}\) is relevant only when \(P_{i,\ell}\) holds. Implementations using SMT datatype selectors must guard constraints involving selectors for absent child positions.

## 3. Canonical slot ordering

The intended canonical ordering is breadth-first traversal, omitting leaves and visiting each non-leaf node only once.

Conceptually:

1. Begin with the root.
2. Assign the root to \(s_0\), provided it is non-leaf.
3. Inspect the children of the root in their given order.
4. Whenever a previously unseen non-leaf child is encountered, assign it to the next unused slot.
5. Ignore leaves when assigning slots.
6. If a non-leaf child has already been assigned a slot, reuse that slot; do not assign another.
7. Continue by inspecting the children of \(s_1\), then \(s_2\), and so forth.

Thus the slot indices correspond to the order of **first encounters of distinct non-leaf nodes**.

This is equivalent to breadth-first traversal of the DAG with duplicate visits suppressed.

It is not necessary to construct explicit BFS frontiers.

The encoding below enforces this ordering declaratively.

## 4. Basic slot constraints

### 4.1 Root assignment

If the root is non-leaf, require

\[
\boxed{s_0=r.}
\]

If the root is a leaf, no slots are required.

To support both cases uniformly, assert

\[
\boxed{
\operatorname{NonLeaf}(r)
\iff
s_0\ne\texttt{null}
}
\]

and

\[
\boxed{
\operatorname{NonLeaf}(r)
\implies
s_0=r.
}
\]

The root itself must be a valid proof node, not `null`.

### 4.2 Active slots form a prefix

Require

\[
\boxed{
s_{i+1}\ne\texttt{null}
\implies
s_i\ne\texttt{null}
}
\]

for every \(0\le i<n-1\).

Consequently, if \(m\) slots are active, they are precisely

\[
s_0,\ldots,s_{m-1},
\]

and the remaining slots contain `null`.

No separate Boolean variables indicating whether slots are active are necessary.

### 4.3 Active slots contain non-leaf nodes

For every \(i\), assert

\[
\boxed{
s_i\ne\texttt{null}
\implies
\operatorname{NonLeaf}(s_i).
}
\]

This ensures that leaf nodes never consume slots.

### 4.4 Distinctness of active slot values

For every \(0\le i<j<n\), assert

\[
\boxed{
s_i\ne\texttt{null}
\land
s_j\ne\texttt{null}
\implies
s_i\ne s_j.
}
\]

Thus no two active slots represent the same proof node.

This requires \(O(n^2)\) pairwise disequalities.

## 5. Child-reference predicates

For every child position \((i,\ell)\) and slot index \(j\), introduce a Boolean variable

\[
E_{i,\ell,j}.
\]

Its meaning is:

\[
E_{i,\ell,j}
\iff
\text{the \(\ell\)th child of \(s_i\) is the node in \(s_j\)}.
\]

More precisely, assert

\[
\boxed{
E_{i,\ell,j}
\iff
P_{i,\ell}
\land
s_j\ne\texttt{null}
\land
C_{i,\ell}=s_j.
}
\]

The presence guard is important: an absent child position must not produce a child reference, regardless of the value returned by an inapplicable datatype selector.

Because active slot values are distinct, at most one \(E_{i,\ell,j}\) can hold for a given child position \((i,\ell)\).

If the child is a leaf, every \(E_{i,\ell,j}\) is false.

If the child is non-leaf, the coverage constraint in Section 8 will require exactly one \(E_{i,\ell,j}\) to hold.

## 6. Discovery predicates

For every child position \((i,\ell)\) and slot index \(j\), introduce a Boolean variable

\[
D_{i,\ell,j}.
\]

Its intended meaning is:

\[
D_{i,\ell,j}
\iff
j=0
\;\lor\;
\exists(p,q)<_{\mathrm{lex}}(i,\ell):
E_{p,q,j}.
\]

Thus \(D_{i,\ell,j}\) is true if either:

- \(j=0\), because the root occupies the first slot; or
- \(s_j\) has already appeared as a child in an earlier child position.

This is a statement about the ordering of the symbolic slots, not about node identifiers stored in the proof datatype.

### 6.1 Predecessor function

Define the predecessor of a child position by

\[
\operatorname{pred}(i,\ell)=
\begin{cases}
(i,\ell-1), & \ell>0,\\[4pt]
(i-1,a-1), & \ell=0\land i>0.
\end{cases}
\]

The first child position \((0,0)\) has no predecessor.

### 6.2 Initialization

For every \(j\), assert

\[
\boxed{
D_{0,0,j}\iff(j=0).
}
\]

In the degenerate case where the root is a leaf and every slot is `null`, this initialization is simply a convention reserving index zero for the root. No child positions are present, so it has no further effect.

### 6.3 Recurrence

For every \((i,\ell)\ne(0,0)\) and every \(j\), let

\[
(p,q)=\operatorname{pred}(i,\ell).
\]

Assert

\[
\boxed{
D_{i,\ell,j}
\iff
D_{p,q,j}\lor E_{p,q,j}.
}
\]

This recurrence accumulates all previous occurrences of \(s_j\).

It is important that the recurrence includes the preceding value of \(D\), rather than merely checking the immediately preceding child reference.

## 7. BFS symmetry-breaking constraints

For every child position \((i,\ell)\) and every \(j>0\), assert

\[
\boxed{
E_{i,\ell,j}
\implies
D_{i,\ell,j-1}.
}
\]

This is the central symmetry-breaking constraint.

It states:

> A child position may refer to slot \(s_j\) only if slot \(s_{j-1}\) has already been encountered at an earlier child position, or \(j-1=0\).

Because the root is initially considered discovered, this forces previously unseen non-leaf nodes to be assigned to slots in increasing index order.

For example, if only \(s_0\) has been discovered, a child position may refer to \(s_0\) or introduce \(s_1\), but it cannot introduce \(s_2\).

Once \(s_1\) has appeared, \(s_2\) may be introduced.

References to previously discovered slots remain unrestricted, allowing DAG sharing.

### 7.1 Every active slot must be discovered before processing it

For every \(1\le i<n\), assert

\[
\boxed{
s_i\ne\texttt{null}
\implies
D_{i,0,i}.
}
\]

This requires every active non-root slot to have appeared as a child before its own child positions are processed.

It excludes unreachable active slots.

Combined with the discovery-order constraints, it ensures that processing slots in increasing index order corresponds to breadth-first traversal.

## 8. Coverage of all non-leaf children

The constraints above restrict references to active slots, but do not by themselves ensure that every non-leaf child is represented by a slot.

An additional coverage constraint is required.

For every child position \((i,\ell)\), assert

\[
\boxed{
P_{i,\ell}
\land
\operatorname{NonLeaf}(C_{i,\ell})
\implies
\bigvee_{j=0}^{n-1}E_{i,\ell,j}.
}
\]

This requires every non-leaf child of every active slot to equal the node assigned to some active slot.

Leaves do not need to satisfy this condition.

Because active slot values are distinct, the matching slot is unique.

The coverage constraint is essential: without it, the solver could construct non-leaf subproofs that are not assigned to any slot and therefore evade the symmetry-breaking constraints.

There are at most \(an\) child positions, and each coverage constraint contains \(n\) alternatives.

For fixed \(a\), the total size of these constraints is \(O(n^2)\).

### 8.1 Validity of present children

If `null` belongs to the same datatype as valid proof nodes, also assert

\[
\boxed{
P_{i,\ell}
\implies
C_{i,\ell}\ne\texttt{null}.
}
\]

This prevents a valid proof node from using the unused-slot sentinel as an actual child.

The remaining requirements for a child to constitute a valid proof premise are imposed by the separate proof-validity encoding.

## 9. Complete constraint summary

The encoding consists of the following constraints.

### Slot structure

For every \(i\):

\[
s_i\ne\texttt{null}
\implies
\operatorname{NonLeaf}(s_i).
\]

For every \(i<n-1\):

\[
s_{i+1}\ne\texttt{null}
\implies
s_i\ne\texttt{null}.
\]

For every \(i<j\):

\[
s_i\ne\texttt{null}
\land
s_j\ne\texttt{null}
\implies
s_i\ne s_j.
\]

### Root

\[
\operatorname{NonLeaf}(r)
\iff
s_0\ne\texttt{null}.
\]

\[
\operatorname{NonLeaf}(r)\implies s_0=r.
\]

### Child references

For every \((i,\ell,j)\):

\[
E_{i,\ell,j}
\iff
P_{i,\ell}
\land
s_j\ne\texttt{null}
\land
C_{i,\ell}=s_j.
\]

### Discovery initialization

For every \(j\):

\[
D_{0,0,j}\iff(j=0).
\]

### Discovery recurrence

For every \((i,\ell)\ne(0,0)\), with

\[
(p,q)=\operatorname{pred}(i,\ell),
\]

and every \(j\):

\[
D_{i,\ell,j}
\iff
D_{p,q,j}\lor E_{p,q,j}.
\]

### Discovery order

For every \((i,\ell)\) and \(j>0\):

\[
E_{i,\ell,j}
\implies
D_{i,\ell,j-1}.
\]

### Reachability

For every \(i>0\):

\[
s_i\ne\texttt{null}
\implies
D_{i,0,i}.
\]

### Non-leaf child coverage

For every \((i,\ell)\):

\[
P_{i,\ell}
\land
\operatorname{NonLeaf}(C_{i,\ell})
\implies
\bigvee_{j=0}^{n-1}E_{i,\ell,j}.
\]

### No null children

For every \((i,\ell)\):

\[
P_{i,\ell}
\implies
C_{i,\ell}\ne\texttt{null}.
\]

## 10. Implementation pseudocode

The following pseudocode describes constraint generation. `assert` means to add the specified Boolean formula to the SMT query.

```python
# Inputs:
#   n: maximum number of non-leaf proof nodes
#   a: maximum child arity (normally 3)
#   r: symbolic proof root
#   s[0:n]: symbolic proof-node slots
#   null: distinguished unused-slot value

# Assumed operations:
#   nonleaf(v)
#   arity(v)
#   child(v, ell)   # meaningful only when ell < arity(v)

def pred(i, ell):
    assert (i, ell) != (0, 0)

    if ell > 0:
        return (i, ell - 1)

    return (i - 1, a - 1)


def present(i, ell):
    return And(
        s[i] != null,
        arity(s[i]) > ell,
    )


# 1. Root assignment.
assert Iff(nonleaf(r), s[0] != null)
assert Implies(nonleaf(r), s[0] == r)

# 2. Active slots form a prefix.
for i in range(n - 1):
    assert Implies(
        s[i + 1] != null,
        s[i] != null,
    )

# 3. Active slots are non-leaf.
for i in range(n):
    assert Implies(
        s[i] != null,
        nonleaf(s[i]),
    )

# 4. Distinct active slot values.
for i in range(n):
    for j in range(i + 1, n):
        assert Implies(
            And(s[i] != null, s[j] != null),
            s[i] != s[j],
        )

# 5. Child-reference variables E.
for i in range(n):
    for ell in range(a):
        for j in range(n):
            E[i, ell, j] = fresh_bool()

            assert Iff(
                E[i, ell, j],
                And(
                    present(i, ell),
                    s[j] != null,
                    child(s[i], ell) == s[j],
                ),
            )

# 6. Discovery variables D.
for i in range(n):
    for ell in range(a):
        for j in range(n):
            D[i, ell, j] = fresh_bool()

# 7. Initialize discovery.
for j in range(n):
    assert Iff(D[0, 0, j], j == 0)

# 8. Accumulate discovery.
for i in range(n):
    for ell in range(a):
        if (i, ell) == (0, 0):
            continue

        p, q = pred(i, ell)

        for j in range(n):
            assert Iff(
                D[i, ell, j],
                Or(
                    D[p, q, j],
                    E[p, q, j],
                ),
            )

# 9. Enforce canonical first-occurrence order.
for i in range(n):
    for ell in range(a):
        for j in range(1, n):
            assert Implies(
                E[i, ell, j],
                D[i, ell, j - 1],
            )

# 10. Every active slot must have been discovered
#     before its child positions are processed.
for i in range(1, n):
    assert Implies(
        s[i] != null,
        D[i, 0, i],
    )

# 11. Cover every non-leaf child with an active slot.
for i in range(n):
    for ell in range(a):
        assert Implies(
            And(
                present(i, ell),
                nonleaf(child(s[i], ell)),
            ),
            Or(*[
                E[i, ell, j]
                for j in range(n)
            ]),
        )

# 12. Present children must not be null.
for i in range(n):
    for ell in range(a):
        assert Implies(
            present(i, ell),
            child(s[i], ell) != null,
        )
```

This pseudocode describes the logical encoding, not a particular SMT API.

In particular, implementations must translate `arity`, `nonleaf`, and `child` into the appropriate constructor tests and selectors for the proof datatype.

The root must also be constrained to be a valid proof node by the surrounding proof-synthesis encoding.

## 11. Why the encoding is canonical

Fix a rooted proof DAG with ordered children.

Assume that all its distinct non-leaf nodes fit within the slot bound \(n\).

We show that the encoding admits exactly one assignment of these nodes to active slots.

### 11.1 Every non-leaf node is represented

The root occupies \(s_0\) if it is non-leaf.

The coverage constraints require every non-leaf child of every active slot to equal some active slot.

By induction over paths from the root, every reachable non-leaf node is represented by an active slot.

Because the DAG is rooted, every node under consideration is reachable.

### 11.2 No non-leaf node is represented twice

The active-slot distinctness constraints require

\[
s_i\ne s_j
\]

for distinct active indices.

Thus each distinct non-leaf node occupies exactly one slot.

### 11.3 Slot order equals first-occurrence order

The discovery predicates identify whether each slot has already been encountered in an earlier child position.

The precedence constraints require the first occurrence of \(s_{j-1}\) to precede the first occurrence of \(s_j\), for every \(j>1\).

The first non-root non-leaf node encountered must therefore occupy \(s_1\), the next distinct non-leaf node must occupy \(s_2\), and so forth.

The reachability constraints ensure that each active slot is encountered before its child positions are processed.

Consequently, scanning the child positions in lexicographic order visits the active slots in breadth-first first-occurrence order.

### 11.4 Uniqueness

For a fixed rooted DAG with ordered children, breadth-first first-occurrence order is uniquely determined.

Therefore, the assignment of non-leaf nodes to active slots is unique.

The remaining slots are `null` by the active-prefix constraint.

Thus the encoding eliminates all symmetry arising solely from permutations of the non-leaf slot assignments.

It does not necessarily eliminate other symmetries in the proof-search problem, such as alternative valid proof structures or commutative inference rules.

## 12. Complexity

There are \(n\) slots and at most \(an\) child positions.

The main costs are:

| Component | Size |
|---|---:|
| Active-prefix constraints | \(O(n)\) |
| Active-slot distinctness | \(O(n^2)\) |
| Child-reference variables \(E\) | \(O(an^2)\) |
| Discovery variables \(D\) | \(O(an^2)\) |
| Discovery recurrences | \(O(an^2)\) |
| First-occurrence constraints | \(O(an^2)\) |
| Reachability constraints | \(O(n)\) |
| Non-leaf child coverage | \(O(an^2)\) |

For fixed maximum arity \(a=3\),

\[
\boxed{
\text{Encoding size}=O(n^2).
}
\]

This is the size of the generated symbolic constraint system, assuming constructor tests, selectors, and node equalities are represented as shared SMT terms rather than repeatedly expanded syntax trees.

The bound does not imply polynomial-time SMT solving. It establishes that eliminating slot-assignment symmetry does not require enumerating exponentially many DAG topologies.

## 13. Implementation considerations

### 13.1 Inductive datatypes versus relational graphs

The construction assumes that the proof-node datatype is inductive, so cyclic constructor structures are impossible.

If child relations are represented independently of an inductive datatype, the surrounding encoding must enforce acyclicity separately.

The BFS constraints alone do not enforce acyclicity.

### 13.2 Do not impose topological index order

Breadth-first first-occurrence numbering is not necessarily a topological ordering.

A later slot may refer to an earlier slot when subproofs are shared.

Therefore, do not additionally require that every child reference point to a slot with a larger index.

Such a constraint could exclude valid proof DAGs.

### 13.3 Absent child positions

An absent child position must satisfy

\[
\neg P_{i,\ell}.
\]

Its corresponding \(E\) variables must all be false.

Do not rely on the values of datatype selectors applied to constructors for which those selectors are inapplicable.

### 13.4 Null representation

The distinguished `null` value is used only to indicate unused slots.

It must be distinguishable from all valid proof nodes.

If `null` is a constructor of the proof-node datatype, constraints must prevent it from appearing as a genuine child in a valid proof.

### 13.5 No node identifiers are required

The indices \(i\) and \(j\) identify symbolic constants in the SMT encoding.

They are not fields of the represented proof nodes.

The encoding uses equality between proof-node values, not an object-level ordering relation.

### 13.6 Leaves are not assigned slots

Leaves may appear directly as children of non-leaf nodes.

Their presence does not advance the canonical slot numbering.

Two distinct leaves therefore need not be compared or assigned an order.

### 13.7 Structural equality and sharing

Distinct active slots must contain distinct datatype values.

If two subproofs are structurally equal under the datatype semantics, they cannot occupy two different active slots.

This is consistent with representing the proof as a DAG with structural sharing.

### 13.8 Separate proof-validity constraints

This document specifies only the slot-assignment and symmetry-breaking constraints.

It does not establish that a node is a valid application of its associated inference rule.

The surrounding proof-synthesis encoding must separately enforce:

- Correct inference-rule applications.
- Formula relationships between premises and conclusions.
- Any required substitution constraints.
- Assumption contexts and discharge conditions.
- The desired root conclusion.
- Any other proof-system-specific well-formedness conditions.

## 14. Recommended tests

The implementation should be tested against small DAGs whose canonical slot assignments can be determined independently.

**Test 1: Single leaf.** The root is a leaf and every slot is `null`.

**Test 2: Single non-leaf node.** The root has only leaf children. Exactly \(s_0\) is active.

**Test 3: Ordered children.** The root has two distinct non-leaf children \(u,v\), in that order. The only permitted assignment is

\[
s_0=r,\quad s_1=u,\quad s_2=v.
\]

**Test 4: Shared child.** The root has children \([u,u]\), where \(u\) is non-leaf. Exactly two slots are active:

\[
s_0=r,\quad s_1=u.
\]

Both child positions refer to \(s_1\).

**Test 5: Leaves interspersed with non-leaf children.** The root has children \([L,u,v]\), where \(L\) is a leaf and \(u,v\) are non-leaf. The canonical assignment is

\[
s_0=r,\quad s_1=u,\quad s_2=v.
\]

The leaf consumes no slot.

**Test 6: Cross-edge to an earlier slot.** A later non-leaf node refers to an already discovered non-leaf node. This must remain satisfiable when the underlying graph is acyclic.

**Test 7: Insufficient slots.** A rooted DAG contains more than \(n\) distinct non-leaf nodes. The constraints must be unsatisfiable.

**Test 8: Unreachable active slot.** An active slot contains a node not reachable from the root. The constraints must be unsatisfiable.

**Test 9: Duplicate active values.** Two active slots contain equal proof-node values. The constraints must be unsatisfiable.

**Test 10: Noncanonical permutation.** Fix a small DAG and permute two non-root slot assignments while preserving the represented graph. Exactly the canonical assignment should satisfy the symmetry-breaking constraints.

For small instances, these tests can be checked exhaustively against a reference BFS implementation.

## 15. Summary

The proposed encoding assigns non-leaf nodes of a rooted, ordered proof DAG to a bounded collection of symbolic slots.

It achieves canonical numbering by combining:

1. A prefix of active, distinct, non-leaf slots.
2. Boolean predicates identifying references from child positions to slots.
3. Boolean predicates recording which slots have appeared in earlier child positions.
4. Precedence constraints forcing first occurrences to follow increasing slot order.
5. Reachability constraints ensuring that active slots are discovered before their children are processed.
6. Coverage constraints ensuring that every non-leaf child is represented by a slot.

The result is a quantifier-free SMT encoding of size

\[
\boxed{O(n^2)}
\]

for maximum child arity three.

It eliminates slot-permutation symmetry without comparing arbitrary node contents, enumerating DAG topologies, or introducing a theory of ordered node identifiers.

## 16. Bounded expression structure for quantifier rules

### 16.1 Objective and challenges

Quantifier introduction and elimination require constraints that inspect the
interior of formulas and terms: substitution, variable occurrence, and binder
scope. Constraining only proof nodes and their immediate conclusions is
insufficient. Every relevant expression descendant must be covered, including
descendants whose structure is chosen by the solver.

Explicitly expanding every possible selector path to a depth bound can produce
exponentially many paths. The plan is instead to expose expression structure
through bounded slot groups, applying local constraints at each represented node
and using child coverage to ensure that no descendants escape those constraints.
The encoding remains a general bounded structural search; it does not restrict
intermediate formulas to a curated collection of templates.

### 16.2 Formula groups attached to proof slots

Keep the proof-slot encoding separate. Introduce an existential-assumption
declaration constructor in the proof datatype. Its conclusion is the instantiated
case assumption generated by an existential elimination. It has no children and
is therefore a leaf, but occupies a proof slot.

Each proof slot owns exactly one formula group, rooted at its conclusion and
containing at most \(m\) non-leaf expression slots. This applies to both inference
nodes and existential-assumption declarations. There is no additional auxiliary
formula group attached to an elimination node and no pool of formula roots to
assign to proof nodes. An unused proof slot has its formula group disabled:
all expression slots are inactive and semantic constraints are guarded.

Within each enabled group, adapt the root, active-prefix, distinctness,
child-coverage, and canonical BFS constraints specified above. Distinctness and
discovery order are local to the group: equal expression values in different
groups are permitted.

Each group represents the DAG of distinct non-leaf subexpression values reachable
from its root. Consequently, \(m\) bounds this DAG, not the number of occurrences
in the expanded syntax tree. Expression leaves consume no expression slots, but
their scope conditions and semantic base cases must still be constrained at roots and present child
positions. Inapplicable datatype selectors must remain guarded.

For \(n\) proof slots, this allocates \(nm\) expression slots. For fixed maximum
expression child arity, the structural constraints occupy \(O(nm^2)\), not
\(O(n^2m^2)\), in addition to the proof encoding. There is no BFS traversal or
pairwise distinctness requirement across all expression groups. These estimates
exclude substitution and other semantic constraints.

The proof budget now counts inference nodes plus existential-assumption
declarations. A proof with \(r\) distinct inference nodes and \(e\) declarations
requires \(r+e\) proof slots. Thus \(n\) is a bound on represented proof objects,
not solely on inference steps. Contextual leaves and assumption-use references
remain outside this slot budget.

### 16.2.1 Declaration ownership and BFS coverage

An existential-assumption declaration can occur as a structural child only in a
dedicated position of an existential-elimination node. Each elimination has one
such declaration, and each declaration has exactly one owner. Use a fixed order
for the elimination's structural children: the existential major premise, the
declaration, and the case proof. The declaration cannot be the query root or an
ordinary proof premise.

Uses of the assumption inside the case proof are reference leaves identifying
the declaration, not additional structural edges to it. Multiple uses may refer
to the same declaration. The declaration's identity must distinguish assumptions
belonging to different owners even if their formulas happen to be equal. These
references participate in assumption-dependency and discharge constraints; they
are not followed by BFS. The declaration child is not an established premise
whose dependencies should simply be unioned into the elimination result.

This extends the non-leaf-only proof encoding in Sections 2–15. Replace its
proof-node slot-eligibility predicate with

\[
\operatorname{NeedsSlot}(v)
\iff \operatorname{Inference}(v)
\lor \operatorname{ExistentialAssumptionDeclaration}(v).
\]

Apply active-slot constructor restrictions, root assignment, and child coverage using this predicate,
while separately excluding declarations as query roots. A declaration is
discovered through its owner's dedicated child position and has zero outgoing
positions. Reachability must be checked at the start of each slot's processing,
including zero-child declarations; discovery state is carried forward unchanged
when there are no children. Ordinary reference and contextual leaves still do
not occupy slots. Expression-group BFS continues to count only non-leaf
expression values.

Inference-rule assertions must be guarded by the inference constructor; declaration
nodes instead satisfy ownership and instantiated-assumption constraints. Formula
coverage applies uniformly to the conclusions of both node kinds.

### 16.2.2 Assumption formulas

Temporary assumptions reference formulas according to the owning inference's
rule and, where applicable, ordered branch position:

| Rule | Temporary assumption formula |
|---|---|
| Implication introduction | Antecedent of the owner's conclusion |
| Disjunction elimination | Corresponding disjunct of the major premise's conclusion |
| Existential elimination | Conclusion of the owner's declaration child |

Implication and disjunction assumptions are existing subformulas and need no
separate expression groups. Disjunction elimination can provide multiple case
assumptions, distinguished by branch position. Assumption identity and dependency
bookkeeping remain separate from formula structure.

Universal introduction proves an opened body in its premise; that body is not a
temporary assumption and is already represented by the premise's conclusion.
Universal elimination and existential introduction also relate premise and
conclusion formulas already represented. Existential elimination gives its opened
case assumption an explicit declaration slot because that formula need not be
the conclusion of any inference.

Concrete contextual leaves have no proof slots; their formulas can be traversed
in the host language. Any such handling must preserve the declared size bounds
and semantic checks. Instantiation terms still need scope and quantifier-domain
constraints, and a bound or coverage justification where their structure is not
already covered by the represented formulas; the conclusion-group layout does
not itself specify a separate term-synthesis encoding.

### 16.3 Substitution as a bounded dynamic-programming computation

Use direct datatype equality for rule relationships that preserve expressions,
such as identifying a conjunct with a premise conclusion. Quantifier rules
instead relate a quantified body to an instance. Encode that transformation by
unrolling a substitution computation over the covered source structure, then
equate its output with the required result formula.

#### 16.3.1 State and binder depth

For one substitution operation with replacement term \(t\), introduce an
expression-valued constant

\[
u_{i,d}=\operatorname{open}_d(s_i,t)
\]

for each relevant source slot \(s_i\) and traversal depth \(d\). Each substitution
operation has its own state family. Depth counts binders crossed inside the body
being opened, not expression-tree depth or the choice of variable to replace.
Traversal starts at depth zero and increments when entering a nested binder.

For example, the body of \(\forall x.(P(x)\land\forall y.R(x,y))\) is

```text
And(P(#0), Forall(R(#1, #0)))
```

Opening the outer binder replaces `#0` in `P` at depth zero and `#1` in `R` at
depth one. The inner `#0` denotes `y` and remains unchanged.

For removal of one binder, the bound-variable leaf equation is

\[
\operatorname{open}_d(\#k,t)=
\begin{cases}
\#k & k<d,\\
\operatorname{shift}_d(t) & k=d,\\
\#(k-1) & k>d.
\end{cases}
\]

Here \(\operatorname{shift}_d\) raises the replacement's externally bound indices
by \(d\), respecting binders internal to the replacement. It is the identity on
nonce variables and terms with no externally bound indices. Non-variable leaves
are preserved unless their constructor has another explicitly specified role in
substitution.

The depth dimension is necessary because structural DAG sharing is independent
of binder context. In `And(P(#0), Forall(P(#0)))`, both occurrences of `P(#0)`
have the same datatype value, but opening the outer binder transforms them
differently. Conversely, substitution can merge different source values or
replace a leaf with a compound term. Therefore source and result BFS indices
must not be assumed to correspond, even for opening with a fresh nonce. A body
that is a subtree of a larger formula group also does not start with its own
independent BFS numbering.

#### 16.3.2 Constructor equations and child routing

The constants \(u_{i,d}\) are computed expression values, not another formula-slot
group. They have no BFS numbering, distinctness, or independent structural budget.
Different states may have equal outputs.

For each relevant state, guard on the source constructor and reconstruct that
constructor with transformed children and preserved non-child payloads. For
example, a binary source node gives

\[
u_{i,d}=\operatorname{Binary}(op,v_L,v_R).
\]

For each present non-leaf source child \(c\), route its transformed value \(v\)
through the source group's coverage:

\[
c=s_k\implies v=u_{k,d'}.
\]

Here \(d'=d\) for ordinary children and is increased by the number of binders
introduced along that child edge. Guard these implications by state relevance,
constructor, and child presence. For leaf children, constrain \(v\) directly by
the leaf equations, allowing a replacement leaf to produce a compound result.
Handle leaf source roots directly as well.

Seed relevance at the body root at depth zero and propagate it through every
recursive obligation. Every relevant non-leaf child must resolve to a covered
source slot and a defined state. Inactive or unreachable states need not impose
scope restrictions. The finite depth range must cover every possible reachable
binder depth under the structural bounds; it must not silently truncate an
obligation. A bound on binder increments and source paths gives such a range.
If an additional traversal bound is used, expose it as a search bound.

Finally, equate the transformed body root with the result formula. Constructor
equalities connect transformed descendants to that result without enumerating
target-slot choices. The result's existing formula group supplies its structural
bound and coverage. This handles merging, splitting by binder context, and
leaf-to-compound replacement without a binary source/result correspondence table.
The source datatype's acyclicity and complete child equations justify the
computation by structural induction; these are finite constraints, not recursive
SMT function definitions.

Replacement shifting also needs a correct bounded implementation when \(t\)
contains externally bound indices. It may use a similar computation over the
replacement structure. This cost is separate from routing source children.
Concrete source expressions can instead be traversed in the host language while
preserving the same equations and bounds.

#### 16.3.3 Size and propagation

For source capacity \(m\), fixed child arity, and \(D\) depth states, one
substitution operation uses \(O(mD)\) transformed-value constants and
\(O(Dm^2)\) child-routing constraints. Constructor equations add \(O(mD)\) size
for a fixed schema. These estimates exclude replacement shifting, variable-length
list handling, and selecting the source group when proof connections are
symbolic. Total query cost also depends on the number of substitution operations
and candidate source groups; the per-operation estimate is not a total bound.

A general binary correspondence encoding has \(m^2\) possible parent pairs;
expanding both child-slot choices for each pair can cost \(O(m^4)\). Factoring
shared child lookups can reduce this to \(O(m^3)\) per context. The functional
encoding avoids that target lookup by storing the transformed expression value
itself. No runtime advantage is guaranteed solely by these size estimates.

Datatype equality can propagate constructor information through the computation
in either direction, even though the equations describe forward substitution.
Independent formula groups still carry their own coverage and discovery costs.
Benchmark both propagation and total solving time rather than treating semantic
sharing as elimination of all duplicated bookkeeping.

### 16.4 Variable representation, scope, and substitution

Represent bound variables with de Bruijn indices. Universal introduction checks
its premise under an extended variable context and relates that premise's
conclusion to the quantified body. Context extension and substitution must shift
indices correctly under nested binders and preserve the interpretation of outer
assumptions. No generated variable names or name-collision tests are needed.

For existential elimination at proof slot \(i\), use a nonce variable \(\nu_i\)
whose identity is determined by that slot. Nonces occupy a namespace disjoint
from ambient variables and are distinct across slots. The conclusion of the
elimination's declaration child represents the existential body instantiated
with \(\nu_i\), using the declaration's own formula group.

Uniqueness of these identities is guaranteed by construction. Scope validity is
a separate invariant: the existential witness must not escape into the
elimination conclusion or its remaining assumption dependencies, and universal
introduction must not generalize a variable on which an undischarged assumption
depends. Enforce these requirements through variable contexts or scope/dependency
constraints, not through searches for fresh names. References to shared proof
nodes must respect their variable contexts. De Bruijn indices must be interpreted
relative to those contexts rather than treated as globally meaningful variables.

Properties determined by a node and its children can be encoded as local
summaries with explicit leaf cases. Occurrence or dependency summaries, where
needed for scope checking, must account for binder context.

Apply the computation in Section 16.3 to relate the quantified body and the
already represented instance. For universal introduction, opening is interpreted
under the extended premise context; the equations must agree with that context's
index convention. Universal elimination and existential introduction use the
chosen instantiation term. Existential elimination uses the owner's nonce and
the declaration child's conclusion as the result. No additional independently
synthesized formula group is required for substitution outputs.

The equations describe opening one binder. Quantifiers introducing multiple
variables, restrictions, or expression-bearing types require explicit binder
transitions for each affected child; they must not be treated as ordinary
children merely because they use the same expression datatype.

### 16.5 Complete coverage of the expression schema

The expression schema includes expressions nested in types and several list
fields, including quantifier premises. The existing finite-operator arity bound
does not bound every such list or every recursive expression path.

Before implementation, specify the child relation, ordering, and bounds for all
relevant constructors, lists, and expression-bearing type fields. Lists must have
bounded, guarded traversal with explicit termination, or their own covered
representation. Leaf payloads, including variable identifiers and bound-variable
indices, need the appropriate domain and scope constraints. A non-leaf expression
budget alone does not bound every payload or establish scope validity.

Do not impose a blanket well-typedness constraint on every generated intermediate
expression. Instead, make type judgments explicit premises of inference rules
whose validity depends on domain membership. In particular, universal elimination
and existential introduction have the forms

\[
\frac{\forall x:T.\,P(x)\qquad t:T}{P(t)}
\qquad
\frac{t:T\qquad P(t)}{\exists x:T.\,P(x)}.
\]

Additional quantifier restrictions likewise require their instantiated premises.
The solver cannot instantiate a restricted quantifier at an arbitrary term
merely because both expressions can be represented by the datatype.

Initially, seed the proof context with a type judgment for each subterm of the
input premises and overall conclusion that does not occur within a binder,
using its externally calculated symbolic type. Do not descend into binding
scopes when collecting these subterms, even for a subterm that does not itself
mention the bound variable.
These are certified contextual facts supplied by the external type analysis, not
unconstrained assumptions the solver may invent. Preserve symbolic type
expressions, including dimensions and other term-dependent components, and
substitute into them when their parameters are instantiated.

Supplied judgments retain any ambient hypotheses or declarations on which their
external type analysis depends. Seeding judgments for occurrences within binders
is deferred: it requires a representation of their local binding contexts and
how those judgments are instantiated when binders are opened. The initial policy
does not export judgments about bound subterms into the ambient proof context.

Initially, these seeded judgments determine which instantiation terms have
available domain evidence. Later, type-deduction rules can derive judgments for
new terms, including terms that are not subterms of the inputs or target. Until
those rules are present, a proof may be unavailable because its required type
judgment is not derivable, even if the term is externally well-typed.

The interpretation of intermediate expressions must still extend the semantics
of well-typed inputs and preserve every encoded rule. Align the decoder's
existing typing checks with this explicit-judgment policy rather than rejecting
intermediates solely for lacking a blanket typing derivation. Structural
constructor checks, binder-scope checks, and validation of required type-judgment
premises remain necessary.

### 16.6 Implementation and validation plan

1. Extend the proof datatype and budget with existential-assumption declarations;
   specify ownership, reference identities, and ordered structural children.
2. Adapt proof BFS to cover declaration leaves, and add one conclusion group per
   proof slot together with rule-directed assumption references and direct
   structural equalities between formulas.
3. Measure the representation on existing propositional cases before adding
   quantifier rules, separating query-construction time from solver time and
   including both satisfiable and insufficient-budget cases.
4. Implement transformed-value states, relevance propagation, constructor
   equations, and leaf substitution with a justified binder-depth bound. Specify
   replacement shifting and the cost of symbolic source-group selection.
5. Validate de Bruijn context handling, slot-owned existential nonces, and scope
   constraints; then add quantifier rules with explicit instantiation-term and
   traversal budgets as needed. Establish the interpretation of intermediate
   expressions and align decoder validation with it.

Validation should cover equal subexpressions within and across groups, leaf
roots, exact size boundaries, hidden descendants through lists and types, and
the same substitution source under different replacements and binder contexts.
Substitution tests should specifically cover a shared source subtree that splits
at different depths, distinct subtrees that merge, leaf-to-compound replacement,
shifting of open replacement terms, decrementation beyond the removed binder,
leaf bodies, and completeness at the maximum reachable depth. Compare evaluated
outputs with an independent host-language substitution implementation. Measure
substitution overhead separately from formula-group and proof-search overhead.
Also validate declaration slot accounting, discovery of zero-child declarations,
unique ownership, rejection of declarations as roots or ordinary premises,
repeated assumption-use references, unused-slot formula groups, multiple
disjunction case assumptions without declaration slots, nested quantifiers with
index shifting, rejection of escaping existential nonces, and rejection of universal generalization over a
variable used by an undischarged assumption. Decoded proofs must continue to
undergo independent semantic checks.

The principal performance risk is the interaction between conditional proof
choices, unknown expression structure, and substitution obligations. Existing
small-query solving times justify measuring this interaction early, but do not
identify BFS or expression-slot count as the bottleneck. The initial design
prioritizes general structural bounds and equality propagation; further
representation optimizations should be driven by these measurements.

### 16.7 Possible direction: occurrence-based expression tree slots

A future alternative is to assign expression slots to non-leaf occurrences in a
tree rather than distinct subexpression values in a DAG. Equal subexpressions at
different positions would occupy separate slots, so active-slot value
distinctness would no longer apply. Slot identity and child references would
need an occurrence-based representation rather than identification by datatype
equality. This change concerns expression groups; proof slots could remain
DAG-based.

For leaf-to-leaf substitution, the expanded tree retains its non-leaf shape even
when nested binders cause identical source subexpressions to transform
differently. If source and result slots are canonically numbered from
corresponding roots, their indices can then correspond directly: constrain
matching constructors and child positions, and apply the appropriate
depth-dependent substitution at leaves. Binder depth still matters, but each
occurrence has a unique path and context. If the source is a subtree of a larger
group, its correspondence needs an explicit mapping or separate traversal
numbering; the enclosing group's indices do not automatically align with the
result's indices. Leaf-to-compound substitution does not preserve this shape.

Such direct constraints may propagate more efficiently than the general
transformed-value computation, which should be tested rather than assumed.
The tradeoff is loss of structural sharing: the bound counts non-leaf
occurrences, and an expanded tree can be exponentially larger than its DAG.
This direction is therefore most attractive where formulas have modest sharing
and shape-preserving substitutions dominate.
