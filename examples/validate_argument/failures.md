# The spectral norm of a wide matrix

Given:

- $A \in \mathbb{R}^{1 \times 2}$

WTS $\left\lVert A \right\rVert_{2} \ge 0$

1. This standard statement for rectangular matrices is rejected by the current validator: $\left\lVert A \right\rVert_{2} \ge 0$.

# The inverse identity for an invertible matrix

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\det(A) \ne 0$

WTS $A^{-1} A = I$

1. The determinant hypothesis says that A is invertible: $\det(A) \ne 0$.
2. The mathematically standard inverse identity is not lowered into the solver: $A^{-1} A = I$.

# Nonnegativity of the Frobenius norm

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $\left\lVert A \right\rVert_{F} \ge 0$

1. The current pipeline handles the two-norm specially but does not establish this equally standard norm claim: $\left\lVert A \right\rVert_{F} \ge 0$.

# A nested quantified statement under conjunction

WTS $\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right) \land x = x$

1. Every real number has itself as a witness: $\exists y \in \mathbb{R}, x = y$.
2. Reflexivity is immediate: $x = x$.

# A quantified premise needed to derive a concrete fact

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\vec{b} \in \mathbb{R}^{2}$
- $\forall \vec{x} \in \mathbb{R}^{2}, A \vec{x} = \vec{b}$

WTS $\vec{b} = \mathbb{0}$

1. Evaluating the universal premise at the zero vector should give the conclusion, but the current validator does not use such a premise as a general solver assertion: $\vec{b} = \mathbb{0}$.

# An existential witness requiring arithmetic reasoning

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. The obvious witness is one, but the current existential matcher does not synthesize it from the arithmetic fact: $x = 1$.

# Zero-based sequence indexing

Given:

- $z \in \operatorname{Seq}_{2}(\mathbb{R})$

WTS $z_{0} \in \mathbb{R}$

1. This zero-based claim is outside the declared one-based sequence, but the current validator accepts it: $z_{0} \in \mathbb{R}$.

# A flat induction proof without explicit obligations

WTS $2^{n} \ge n + 1$ by induction on $n$

1. The base case is immediate: $2^{0} \ge 0 + 1$.
2. Checking the first few natural numbers suggests the claim, but the induction hypothesis is not represented as a nested given: $2^{n} \ge n + 1$.

# The Gram matrix proof needs an explicitly introduced arbitrary vector

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $\operatorname{Nul}(A^\top A) = \operatorname{Nul}(A)$

1. A standard proof starts with an arbitrary vector, but this free proof variable is not introduced by the goal: $A^\top A \vec{x} = \mathbb{0} \implies A \vec{x} = \mathbb{0}$.

# A linear-independence definition with quantified coefficients

Given:

- $\vec{v}_{1} \in \mathbb{R}^{2}$
- $\vec{v}_{2} \in \mathbb{R}^{2}$
- $\det(\begin{bmatrix}\vec{v}_{1} & \vec{v}_{2}\end{bmatrix}) \ne 0$

WTS $\forall a \in \mathbb{R}, b \in \mathbb{R}, a \vec{v}_{1} + b \vec{v}_{2} = \mathbb{0} \implies a = 0 \land b = 0$

1. This standard characterization combines quantified vector equations with determinant reasoning: $a \vec{v}_{1} + b \vec{v}_{2} = \mathbb{0} \implies a = 0 \land b = 0$.

# A matrix square-root identity with unverified existence

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$

1. The square-root definition gives the identity: $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$.

# Componentwise ordering of vectors

Given:

- $\vec{x} \in \mathbb{R}^{2}$
- $\vec{y} \in \mathbb{R}^{2}$
- $\vec{x} < \vec{y}$

WTS $\vec{x} < \vec{y}$

1. The componentwise comparison is repeated as the conclusion: $\vec{x} < \vec{y}$.
