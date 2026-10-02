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
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $\det(A) \ne 0$
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

quantifiers embedded beneath another operator are unsupported
</details>

1. $\exists y \in \mathbb{R}, x = y$

   <details>
   <summary>Inconclusive</summary>

   quantifier body contains unbound variable x
   </details>
2. $x = x$

   <details>
   <summary>Unsupported step</summary>

   missing type for x
   </details>

# A quantified premise needed to derive a concrete fact

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $b \in \mathbb{R}^{2}$
- $\forall x \in \mathbb{R}^{2}, A x = b$

WTS $b = \mathbb{0}$

<details>
<summary>❌ counterexample found</summary>

The negation of $b = \mathbb{0}$ is satisfied by:

- $A = \begin{bmatrix}\square & \square \\ \square & \square\end{bmatrix}$
- $b = \begin{bmatrix}-1 \\ -1\end{bmatrix}$
</details>

1. $b = \mathbb{0}$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $b = \mathbb{0}$ is satisfied by:

   - $A = \begin{bmatrix}\square & \square \\ \square & \square\end{bmatrix}$
   - $b = \begin{bmatrix}-1 \\ -1\end{bmatrix}$
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

   missing type for x
   </details>

# Zero-based sequence indexing

Given:

- $z \in \operatorname{Seq}_{2}(\mathbb{R})$

WTS $z_{0} \in \mathbb{R}$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
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

   missing type for n
   </details>

# The Gram matrix proof needs an explicitly introduced arbitrary vector

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $\operatorname{Nul}(A^\top A) = \operatorname{Nul}(A)$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. $A^\top A x = \mathbb{0} \implies A x = \mathbb{0}$

   <details>
   <summary>Unsupported step</summary>

   missing type for x
   </details>

# A linear-independence definition with quantified coefficients

Given:

- $v_{1} \in \mathbb{R}^{2}$
- $v_{2} \in \mathbb{R}^{2}$
- $\det(\begin{bmatrix}v_{1} & v_{2}\end{bmatrix}) \ne 0$

WTS $\forall a \in \mathbb{R}, b \in \mathbb{R}, a v_{1} + b v_{2} = \mathbb{0} \implies a = 0 \land b = 0$

1. $a v_{1} + b v_{2} = \mathbb{0} \implies a = 0 \land b = 0$

## Error

subscripted expression is not a sequence

# A matrix square-root identity with unverified existence

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. $A^{\frac{1}{2}} A^{\frac{1}{2}} = A$

   <details>
   <summary>⚠️ conditional</summary>

   The existence of $A^{\frac{1}{2}}$ was assumed without checking.
   </details>

# Componentwise ordering of vectors

Given:

- $x \in \mathbb{R}^{2}$
- $y \in \mathbb{R}^{2}$
- $x < y$

WTS $x < y$

1. $x < y$

## Error

matrix ordering comparisons are not supported
