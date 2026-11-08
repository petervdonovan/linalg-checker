# Contextual reuse

Context:

- $p$

Goal: $p$

Limits: 0 rule slots, 3 premises per inference.

Found proof.

This statement is already established in the current context.

# Binary introduction

Context:

- $p$
- $q$

Goal: $p \land q$

Limits: 1 rule slots, 3 premises per inference.

Found proof.

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

Limits: 1 rule slots, 3 premises per inference.

Found proof.

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

Limits: 1 rule slots, 3 premises per inference.

no proof within encoding and budget (1 rule slots, 3 premises)

# Nested introduction: sufficient slots

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 2 rule slots, 3 premises per inference.

Found proof.

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

Limits: 4 rule slots, 2 premises per inference.

no proof within encoding and budget (4 rule slots, 2 premises)

# Flat conjunction: capacity three

Context:

- $p$
- $q$
- $r$

Goal: $p \land q \land r$

Limits: 1 rule slots, 3 premises per inference.

Found proof.

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

Limits: 2 rule slots, 3 premises per inference.

Found proof.

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

Limits: 3 rule slots, 3 premises per inference.

no proof within encoding and budget (3 rule slots, 3 premises)

# Shared descendant: four distinct nodes

Context:

- $p$
- $q$
- $r$
- $s$

Goal: $p \land q \land r \land p \land q \land s$

Limits: 4 rule slots, 3 premises per inference.

Found proof.

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

Limits: 2 rule slots, 3 premises per inference.

no proof within encoding and budget (2 rule slots, 3 premises)

# Elimination is not an available rule

Context:

- $p \land q$

Goal: $p$

Limits: 2 rule slots, 3 premises per inference.

no proof within encoding and budget (2 rule slots, 3 premises)
