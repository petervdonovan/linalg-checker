# The spectral norm of a wide matrix

Given:

- $A \in \mathbb{R}^{1 \times 2}$

WTS $\left\lVert A \right\rVert_{2} \ge 0$

<details>
<summary>⚠️ dimensionally invalid</summary>

This step is not dimensionally meaningful in the following environment:

- $A \in \mathbb{R}^{1 \times 2}$
</details>

1. $\left\lVert A \right\rVert_{2} \ge 0$

   <details>
   <summary>⚠️ dimensionally invalid</summary>

   This step is not dimensionally meaningful in the following environment:

   - $A \in \mathbb{R}^{1 \times 2}$
   </details>

# The inverse identity for an invertible matrix

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\det(A) \ne 0$

WTS $A^{-1} A = I$

<details>
<summary>Unsupported step</summary>

unary operator remains after concrete elaboration
</details>

1. $\det(A) \ne 0$

   <details>
   <summary>✅ repeats established fact</summary>

   This statement is already established in the current context.
   </details>
2. $A^{-1} A = I$

   <details>
   <summary>Unsupported step</summary>

   unary operator remains after concrete elaboration
   </details>

# Nonnegativity of the Frobenius norm

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $\left\lVert A \right\rVert_{F} \ge 0$

<details>
<summary>Unsupported step</summary>

unary operator remains after concrete elaboration
</details>

1. $\left\lVert A \right\rVert_{F} \ge 0$

   <details>
   <summary>Unsupported step</summary>

   unary operator remains after concrete elaboration
   </details>

# A nested quantified statement under conjunction

WTS $\forall x \in \mathbb{R}, \left(\exists y \in \mathbb{R}, x = y\right) \land x = x$

<details>
<summary>Inconclusive</summary>

verification failed to handle the quantifiers in this formula
</details>

1. $\exists y \in \mathbb{R}, x = y$

   <details>
   <summary>Inconclusive</summary>

   reference to undefined variable $x$
   </details>
2. $x = x$

   <details>
   <summary>Unsupported step</summary>

   reference to undefined variable $x$
   </details>

# A quantified premise needed to derive a concrete fact

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\vec{b} \in \mathbb{R}^{2}$
- $\forall \vec{x} \in \mathbb{R}^{2}, A \vec{x} = \vec{b}$

WTS $\vec{b} = \mathbb{0}$

<details>
<summary>❌ counterexample found</summary>

The negation of $\vec{b} = \mathbb{0}$ is satisfied by:

- $A = \begin{bmatrix}\square & \square \\ \square & \square\end{bmatrix}$
- $\vec{b} = \begin{bmatrix}\square \\ 2\end{bmatrix}$
</details>

1. $\vec{b} = \mathbb{0}$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $\vec{b} = \mathbb{0}$ is satisfied by:

   - $A = \begin{bmatrix}\square & \square \\ \square & \square\end{bmatrix}$
   - $\vec{b} = \begin{bmatrix}\square \\ 2\end{bmatrix}$
   </details>

# An existential witness requiring arithmetic reasoning

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

<details>
<summary>Inconclusive</summary>

no common syntactic witness was established
</details>

1. $x = 1$

   <details>
   <summary>Unsupported step</summary>

   reference to undefined variable $x$
   </details>

# Zero-based sequence indexing

Given:

- $z \in \operatorname{Seq}_{2}(\mathbb{R})$

WTS $z_{0} \in \mathbb{R}$

<details>
<summary>✅ repeats established fact</summary>

This statement is already established in the current context.
</details>

1. $z_{0} \in \mathbb{R}$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# A flat induction proof without explicit obligations

WTS $2^{n} \ge n + 1$ by induction on $n$

<details>
<summary>⚠️ valid claim, incomplete subgoals</summary>

No counterexample was found, but the following subgoals were not established:

- $2^{0} \ge 0 + 1$
- $\forall 2^{n} \ge n + 1, 2^{n + 1} \ge n + 1 + 1$
</details>

1. $2^{0} \ge 0 + 1$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. $2^{n} \ge n + 1$

   <details>
   <summary>Unsupported step</summary>

   reference to undefined variable $n$
   </details>

# The Gram matrix proof needs an explicitly introduced arbitrary vector

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $\operatorname{Nul}(A^\top A) = \operatorname{Nul}(A)$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. $A^\top A \vec{x} = \mathbb{0} \implies A \vec{x} = \mathbb{0}$

   <details>
   <summary>Unsupported step</summary>

   reference to undefined variable $\vec{x}$
   </details>

# A linear-independence definition with quantified coefficients

Given:

- $\vec{v}_{1} \in \mathbb{R}^{2}$
- $\vec{v}_{2} \in \mathbb{R}^{2}$
- $\det(\begin{bmatrix}\vec{v}_{1} & \vec{v}_{2}\end{bmatrix}) \ne 0$

WTS $\forall a \in \mathbb{R}, b \in \mathbb{R}, a \vec{v}_{1} + b \vec{v}_{2} = \mathbb{0} \implies a = 0 \land b = 0$

<details>
<summary>Inconclusive</summary>

subscripted expression is not a sequence
</details>

1. $a \vec{v}_{1} + b \vec{v}_{2} = \mathbb{0} \implies a = 0 \land b = 0$

# A matrix square-root identity with unverified existence

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$

<details>
<summary>⚠️ conditional</summary>

The existence of $A^{\frac{1}{2}}$ was assumed without checking.
</details>

1. $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$

   <details>
   <summary>⚠️ conditional</summary>

   The existence of $A^{\frac{1}{2}}$ was assumed without checking.
   </details>

# Componentwise ordering of vectors

Given:

- $\vec{x} \in \mathbb{R}^{2}$
- $\vec{y} \in \mathbb{R}^{2}$
- $\vec{x} < \vec{y}$

WTS $\vec{x} < \vec{y}$

1. $\vec{x} < \vec{y}$

## Error

matrix ordering comparisons are not supported
