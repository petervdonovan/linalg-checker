# Contextual reuse

Context:

- $p$

Goal: $p$

Limits: 0 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p$.

This statement is already established in the current context.

# Binary introduction

Context:

- $p$
- $q$

Goal: $p \land q$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (2): $p$, $q$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$

Proof tree:

$$
\dfrac{p \qquad q}{p \land q}\;(\land I)
$$

# Three-premise introduction

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (3): $p$, $q$, $r$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$
- $r$

Proof tree:

$$
\dfrac{p \qquad q \qquad r}{p \land q \land r}\;(\land I)
$$

# Nested introduction: insufficient slots

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (1 rule slots, 3 premises, finop arity 3, root dependencies unbounded)

# Nested introduction: sufficient slots

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (3): $p$, $q$, $r$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$
- $r$

Proof tree:

$$
\dfrac{p \qquad \dfrac{q \qquad r}{q \land r}\;(\land I)}{p \land q \land r}\;(\land I)
$$

# Flat conjunction: capacity two

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 4 rule slots, 2 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (4 rule slots, 2 premises, finop arity 3, root dependencies unbounded)

# Flat conjunction: capacity three

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (3): $p$, $q$, $r$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$
- $r$

Proof tree:

$$
\dfrac{p \qquad q \qquad r}{p \land q \land r}\;(\land I)
$$

# Repeated subproof

Context:

- $p$
- $q$

Goal: $p \land q \land p \land q$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (2): $p$, $q$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$

Proof tree:

$$
\dfrac{\dfrac{p \qquad q}{p \land q}\;(\land I) \qquad \dfrac{p \qquad q}{p \land q}\;(\land I)}{p \land q \land p \land q}\;(\land I)
$$

# Shared descendant: insufficient distinct-node budget

Context:

- $p$
- $q$
- $r$
- $s$

Goal: $p \land q \land r \land p \land q \land s$

Limits: 3 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (3 rule slots, 3 premises, finop arity 3, root dependencies unbounded)

# Shared descendant: four distinct nodes

Context:

- $p$
- $q$
- $r$
- $s$

Goal: $p \land q \land r \land p \land q \land s$

Limits: 4 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (4): $p$, $q$, $r$, $s$.

Combined the established conjuncts.

Supporting facts:

- $p$
- $q$
- $r$
- $s$

Proof tree:

$$
\dfrac{\dfrac{\dfrac{p \qquad q}{p \land q}\;(\land I) \qquad r}{p \land q \land r}\;(\land I) \qquad \dfrac{\dfrac{p \qquad q}{p \land q}\;(\land I) \qquad s}{p \land q \land s}\;(\land I)}{p \land q \land r \land p \land q \land s}\;(\land I)
$$

# Missing contextual premise

Context:

- $p$

Goal: $p \land q$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (2 rule slots, 3 premises, finop arity 3, root dependencies unbounded)

# Conjunction elimination

Context:

- $p \land q$

Goal: $p$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p \land q$.

Selected conjunct 1.

Supporting facts:

- $p \land q$

Proof tree:

$$
\dfrac{p \land q}{p}\;(\land E_{1})
$$

# Third conjunct of an n-ary assumption

Context:

- $p \land q \land r$

Goal: $r$

Limits: 1 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $p \land q \land r$.

Selected conjunct 3.

Supporting facts:

- $p \land q \land r$

Proof tree:

$$
\dfrac{p \land q \land r}{r}\;(\land E_{3})
$$

# Nested conjunction elimination

Context:

- $p \land q \land r$

Goal: $r$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $p \land q \land r$.

Selected conjunct 2.

Supporting facts:

- $p \land q \land r$

Proof tree:

$$
\dfrac{\dfrac{p \land q \land r}{q \land r}\;(\land E_{2})}{r}\;(\land E_{2})
$$

# Projection under implication introduction

Context:

(empty)

Goal: $p \land q \implies q$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p \land q$

Proof tree:

$$
\dfrac{\dfrac{\left[p \land q\right]^{a_{1}}}{q}\;(\land E_{2})}{p \land q \implies q}\;(\Rightarrow I\,[a_{1}])
$$

# Temporary assumption identity

Context:

(empty)

Goal: $p \implies p$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Proof tree:

$$
\dfrac{\left[p\right]^{a_{1}}}{p \implies p}\;(\Rightarrow I\,[a_{1}])
$$

# One temporary assumption used twice

Context:

(empty)

Goal: $p \implies p \land p$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}} \qquad \left[p\right]^{a_{1}}}{p \land p}\;(\land I)}{p \implies p \land p}\;(\Rightarrow I\,[a_{1}])
$$

# Vacuous inner discharge

Context:

(empty)

Goal: $p \implies \left(q \implies p\right)$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}}}{q \implies p}\;(\Rightarrow I)}{p \implies \left(q \implies p\right)}\;(\Rightarrow I\,[a_{1}])
$$

# Nested discharges

Context:

(empty)

Goal: $p \implies \left(q \implies p \land q\right)$

Limits: 3 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s) at the final inference.

Discharged assumptions:

- $a_{1}$: $p$
- $a_{2}$: $q$

Proof tree:

$$
\dfrac{\dfrac{\dfrac{\left[p\right]^{a_{1}} \qquad \left[q\right]^{a_{2}}}{p \land q}\;(\land I)}{q \implies p \land q}\;(\Rightarrow I\,[a_{2}])}{p \implies \left(q \implies p \land q\right)}\;(\Rightarrow I\,[a_{1}])
$$

# Independent closed branches

Context:

(empty)

Goal: $\left(p \implies p\right) \land \left(q \implies q\right)$

Limits: 3 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Combined the established conjuncts.

Discharged assumptions:

- $a_{1}$: $p$
- $a_{2}$: $q$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}}}{p \implies p}\;(\Rightarrow I\,[a_{1}]) \qquad \dfrac{\left[q\right]^{a_{2}}}{q \implies q}\;(\Rightarrow I\,[a_{2}])}{\left(p \implies p\right) \land \left(q \implies q\right)}\;(\land I)
$$

# Temporary assumption cannot escape a sibling

Context:

(empty)

Goal: $\left(p \implies p\right) \land p$

Limits: 3 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (3 rule slots, 3 premises, finop arity 3, root dependencies unbounded)

# Remaining ambient dependency

Context:

- $q$

Goal: $p \implies p \land q$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $q$.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Supporting facts:

- $q$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}} \qquad q}{p \land q}\;(\land I)}{p \implies p \land q}\;(\Rightarrow I\,[a_{1}])
$$

# Root dependency bound zero

Context:

- $q$

Goal: $p \implies p \land q$

Limits: 2 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

no proof within encoding and budget (2 rule slots, 3 premises, finop arity 3, root dependencies 0)

# One ambient assumption used twice

Context:

- $p$

Goal: $p \land p$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $p$.

Combined the established conjuncts.

Supporting facts:

- $p$

Proof tree:

$$
\dfrac{p \qquad p}{p \land p}\;(\land I)
$$

# First disjunct

Context:

- $p$

Goal: $p \lor q \lor r$

Limits: 1 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $p$.

Established disjunct 1.

Supporting facts:

- $p$

Proof tree:

$$
\dfrac{p}{p \lor q \lor r}\;(\lor I_{1})
$$

# Middle disjunct

Context:

- $q$

Goal: $p \lor q \lor r$

Limits: 1 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $q$.

Established disjunct 2.

Supporting facts:

- $q$

Proof tree:

$$
\dfrac{q}{p \lor q \lor r}\;(\lor I_{2})
$$

# Last disjunct

Context:

- $r$

Goal: $p \lor q \lor r$

Limits: 1 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $r$.

Established disjunct 3.

Supporting facts:

- $r$

Proof tree:

$$
\dfrac{r}{p \lor q \lor r}\;(\lor I_{3})
$$

# Nested disjunction introduction

Context:

- $q$

Goal: $p \lor q \lor r$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $q$.

Established disjunct 2.

Supporting facts:

- $q$

Proof tree:

$$
\dfrac{\dfrac{q}{q \lor r}\;(\lor I_{1})}{p \lor q \lor r}\;(\lor I_{2})
$$

# Disjunction under implication introduction

Context:

(empty)

Goal: $p \implies p \lor q$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}}}{p \lor q}\;(\lor I_{1})}{p \implies p \lor q}\;(\Rightarrow I\,[a_{1}])
$$

# Closed implication as a disjunct

Context:

(empty)

Goal: $\left(p \implies p\right) \lor q$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Established disjunct 1.

Discharged assumptions:

- $a_{1}$: $p$

Proof tree:

$$
\dfrac{\dfrac{\left[p\right]^{a_{1}}}{p \implies p}\;(\Rightarrow I\,[a_{1}])}{\left(p \implies p\right) \lor q}\;(\lor I_{1})
$$

# Disjunction has no established operand

Context:

(empty)

Goal: $p \lor q$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (2 rule slots, 1 premises, finop arity 3, root dependencies unbounded)

# Disjunction does not eliminate

Context:

- $p \lor q$

Goal: $p$

Limits: 2 rule slots, 1 premises per inference, finop arity 3, unbounded root dependencies.

no proof within encoding and budget (2 rule slots, 1 premises, finop arity 3, root dependencies unbounded)

# Binary disjunction case analysis

Context:

- $p \lor q$

Goal: $q \lor p$

Limits: 3 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p \lor q$.

- Case 1 ($p$): discharged 1 assumption(s).
- Case 2 ($q$): discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$
- $a_{2}$: $q$

Supporting facts:

- $p \lor q$

Proof tree:

$$
\dfrac{p \lor q \qquad \dfrac{\left[p\right]^{a_{1}}}{q \lor p}\;(\lor I_{2}) \qquad \dfrac{\left[q\right]^{a_{2}}}{q \lor p}\;(\lor I_{1})}{q \lor p}\;(\lor E\,[a_{1},a_{2}])
$$

# Ternary disjunction case analysis

Context:

- $p \lor q \lor r$

Goal: $r \lor q \lor p$

Limits: 4 rule slots, 4 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p \lor q \lor r$.

- Case 1 ($p$): discharged 1 assumption(s).
- Case 2 ($q$): discharged 1 assumption(s).
- Case 3 ($r$): discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$
- $a_{2}$: $q$
- $a_{3}$: $r$

Supporting facts:

- $p \lor q \lor r$

Proof tree:

$$
\dfrac{p \lor q \lor r \qquad \dfrac{\left[p\right]^{a_{1}}}{r \lor q \lor p}\;(\lor I_{3}) \qquad \dfrac{\left[q\right]^{a_{2}}}{r \lor q \lor p}\;(\lor I_{2}) \qquad \dfrac{\left[r\right]^{a_{3}}}{r \lor q \lor p}\;(\lor I_{1})}{r \lor q \lor p}\;(\lor E\,[a_{1},a_{2},a_{3}])
$$

# Nested case analysis

Context:

- $p \lor q \lor p$

Goal: $p \lor q$

Limits: 4 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p \lor q \lor p$.

- Case 1 ($p$): discharged 1 assumption(s).
- Case 2 ($q \lor p$): discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$
- $a_{2}$: $q \lor p$
- $a_{3}$: $q$

Supporting facts:

- $p \lor q \lor p$

Proof tree:

$$
\dfrac{p \lor q \lor p \qquad \dfrac{\left[p\right]^{a_{1}}}{p \lor q}\;(\lor I_{1}) \qquad \dfrac{\left[q \lor p\right]^{a_{2}} \qquad \dfrac{\left[q\right]^{a_{3}}}{p \lor q}\;(\lor I_{2}) \qquad \dfrac{\left[p\right]^{a_{1}}}{p \lor q}\;(\lor I_{1})}{p \lor q}\;(\lor E\,[a_{3},a_{1}])}{p \lor q}\;(\lor E\,[a_{1},a_{2}])
$$

# Shared case proof

Context:

- $p \lor p$

Goal: $p$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (1): $p \lor p$.

- Case 1 ($p$): discharged 1 assumption(s).
- Case 2 ($p$): discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p$

Supporting facts:

- $p \lor p$

Proof tree:

$$
\dfrac{p \lor p \qquad \left[p\right]^{a_{1}} \qquad \left[p\right]^{a_{1}}}{p}\;(\lor E\,[a_{1}])
$$

# Vacuous case discharge

Context:

- $p \lor q$
- $r$

Goal: $r$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (2): $p \lor q$, $r$.

- Case 1 ($p$): discharged 0 assumption(s) (vacuous discharge).
- Case 2 ($q$): discharged 0 assumption(s) (vacuous discharge).

Supporting facts:

- $p \lor q$
- $r$

Proof tree:

$$
\dfrac{p \lor q \qquad r \qquad r}{r}\;(\lor E)
$$

# Case analysis retains source dependencies

Context:

- $p \lor p$

Goal: $p$

Limits: 1 rule slots, 3 premises per inference, finop arity 3, 0 root dependencies.

no proof within encoding and budget (1 rule slots, 3 premises, finop arity 3, root dependencies 0)

# Implication elimination

Context:

- $p \implies q$
- $p$

Goal: $q$

Limits: 1 rule slots, 2 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (2): $p \implies q$, $p$.

Applied the established implication to its established antecedent.

Supporting facts:

- $p \implies q$
- $p$

Proof tree:

$$
\dfrac{p \implies q \qquad p}{q}\;(\Rightarrow E)
$$

# Chained implication elimination

Context:

- $p \implies q$
- $q \implies r$
- $p$

Goal: $r$

Limits: 2 rule slots, 2 premises per inference, finop arity 3, unbounded root dependencies.

Found proof.

Remaining assumptions (3): $p \implies q$, $q \implies r$, $p$.

Applied the established implication to its established antecedent.

Supporting facts:

- $q \implies r$
- $p \implies q$
- $p$

Proof tree:

$$
\dfrac{q \implies r \qquad \dfrac{p \implies q \qquad p}{q}\;(\Rightarrow E)}{r}\;(\Rightarrow E)
$$

# Implication elimination under introduction

Context:

- $p \implies q$

Goal: $p \land r \implies q$

Limits: 3 rule slots, 2 premises per inference, finop arity 3, 1 root dependencies.

Found proof.

Remaining assumptions (1): $p \implies q$.

Discharged 1 assumption(s).

Discharged assumptions:

- $a_{1}$: $p \land r$

Supporting facts:

- $p \implies q$

Proof tree:

$$
\dfrac{\dfrac{p \implies q \qquad \dfrac{\left[p \land r\right]^{a_{1}}}{p}\;(\land E_{1})}{q}\;(\Rightarrow E)}{p \land r \implies q}\;(\Rightarrow I\,[a_{1}])
$$

# Closed modus ponens

Context:

(empty)

Goal: $\left(p \implies q\right) \land p \implies q$

Limits: 4 rule slots, 2 premises per inference, finop arity 3, 0 root dependencies.

Found proof.

Remaining assumptions (0): none.

Discharged 2 assumption(s).

Discharged assumptions:

- $a_{1}$: $\left(p \implies q\right) \land p$
- $a_{2}$: $\left(p \implies q\right) \land p$

Proof tree:

$$
\dfrac{\dfrac{\dfrac{\left[\left(p \implies q\right) \land p\right]^{a_{1}}}{p \implies q}\;(\land E_{1}) \qquad \dfrac{\left[\left(p \implies q\right) \land p\right]^{a_{2}}}{p}\;(\land E_{2})}{q}\;(\Rightarrow E)}{\left(p \implies q\right) \land p \implies q}\;(\Rightarrow I\,[a_{1},a_{2}])
$$

# Implication elimination blocked by dependency bound

Context:

- $p \implies q$
- $p$

Goal: $q$

Limits: 1 rule slots, 2 premises per inference, finop arity 3, 1 root dependencies.

no proof within encoding and budget (1 rule slots, 2 premises, finop arity 3, root dependencies 1)
