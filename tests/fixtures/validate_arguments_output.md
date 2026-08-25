# Scalar argument

Given:

- $x \in \mathbb{R}$

WTS $x = x$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. $x = x$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. $x = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $x = 0$ is satisfied by:

   - $x = 2$
   </details>

# Matrix argument

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

<details>
<summary>❌ counterexample found</summary>

The negation of $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$ is satisfied by:

- $A = \begin{bmatrix}2 & \square \\ \square & \square\end{bmatrix}$
</details>

1. $A = A$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# Sequence norm sum

Given:

- $\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})$

WTS $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$

<details>
<summary>❌ counterexample found</summary>

The negation of $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$ is satisfied by:

- $d = 1$
- $n = 1$
- $\vec{z}_{1} = \begin{bmatrix}2\end{bmatrix}$
</details>

1. $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} \ge 0$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Negating an inequality

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $x < y$

WTS $-x > -y$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $x < y$
</details>

1. $-x < -y$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $-x < -y$ is satisfied by:

   - $x = 0$
   - $y = \frac{1}{2}$
   </details>

# Independent implicit matrix constants

WTS $\mathbb{0} = \begin{bmatrix}0 \\ 0\end{bmatrix}$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. $I = \begin{bmatrix}1\end{bmatrix}$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. $I = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
3. $\mathbb{0} = \begin{bmatrix}0 & 0\end{bmatrix}$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# One-sided orthogonality

Given:

- $U^\top U = I$

WTS $U U^\top = I$

<details>
<summary>❌ counterexample found</summary>

The negation of $U U^\top = I$ is satisfied by:

- $U = \begin{bmatrix}\frac{1}{4} \\ \left(\frac{15}{16}\right)^{\frac{1}{2}}\end{bmatrix}$
</details>

# Logic-chain preprocessing

Given:

- $x \in \mathbb{R}$
- $x = 0$

WTS $x = 0 \iff x \le 0 \implies x = x$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $x = 0$
</details>

# Scalar square roots

Given:

- $x \in \mathbb{R}$
- $x \ge 0$

WTS $x^{\frac{1}{2}} \ge 0$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

# Potentially undefined square root

Given:

- $x \in \mathbb{R}$

WTS $x^{\frac{1}{2}} = x^{\frac{1}{2}}$

<details>
<summary>⚠️ conditional</summary>

The expression $x^{\frac{1}{2}}$ may be undefined. For example:

- $x = -1$
</details>

# Assumed matrix square root

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

<details>
<summary>⚠️ conditional</summary>

The existence of $A^{\frac{1}{2}}$ was assumed without checking.
</details>

# Dimensionally invalid matrix square root

Given:

- $A \in \mathbb{R}^{2}$

WTS $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

<details>
<summary>⚠️ dimensionally invalid</summary>

This step is not dimensionally meaningful in the following environment:

- $A \in \mathbb{R}^{2}$
</details>

# Vector two-norm

Given:

- $v \in \mathbb{R}^{2}$

WTS $\left\lVert v \right\rVert_{2} \ge 0$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

# Wide matrix two-norm

Given:

- $A \in \mathbb{R}^{1 \times 2}$

WTS $\left\lVert A \right\rVert_{2} \ge 0$

<details>
<summary>⚠️ dimensionally invalid</summary>

This step is not dimensionally meaningful in the following environment:

- $A \in \mathbb{R}^{1 \times 2}$
</details>

1. $\left\lVert A \right\rVert_{2}^{2} \ge 0$

   <details>
   <summary>Unsupported step</summary>

   a cast to real requires a real scalar or real-valued 1x1 matrix
   </details>

# Block multiplication formula

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$
- $C \in \mathbb{R}^{2 \times 2}$
- $D \in \mathbb{R}^{2 \times 2}$
- $E \in \mathbb{R}^{2 \times 2}$
- $F \in \mathbb{R}^{2 \times 2}$
- $G \in \mathbb{R}^{2 \times 2}$
- $H \in \mathbb{R}^{2 \times 2}$

WTS $\begin{bmatrix}A & B \\ C & D\end{bmatrix} \begin{bmatrix}E & F \\ G & H\end{bmatrix} = \begin{bmatrix}A E + B G & A F + B H \\ C E + D G & C F + D H\end{bmatrix}$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

# Block selector identity

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$

WTS $\begin{bmatrix}A & B\end{bmatrix} \begin{bmatrix}I \\ \mathbb{0}\end{bmatrix} = A$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

# Nested error localization

Given:

- $x \in \mathbb{R}$

WTS $x = x$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. WTS $x = x$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

   1. $x = 0$

      <details>
      <summary>❌ counterexample found</summary>

      The negation of $x = 0$ is satisfied by:

      - $x = 2$
      </details>
   2. $x = x$

      <details>
      <summary>✅ verified</summary>

      No premises seemed necessary to show this.
      </details>
2. $x = x$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# Local givens and sibling names

WTS $0 = 0$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>

1. Given:

   - $y \in \mathbb{R}$

   WTS $y = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $y = 0$ is satisfied by:

   - $y = 2$
   </details>
2. Given:

   - $y \in \mathbb{R}$

   WTS $y = y$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# Squaring nonnegative reals

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $0 \le x$
- $x \le y$

WTS $x x \le y y$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $\left(y - x\right) \left(x + y\right) \ge 0$
</details>

1. WTS $0 \le y$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le y$
   </details>

   1. $x \le y$

      <details>
      <summary>✅ verified</summary>

      This follows from the following facts:

      - $x \le y$
      </details>
   2. $0 \le y$

      <details>
      <summary>✅ verified</summary>

      This follows from the following facts:

      - $0 \le x$
      - $x \le y$
      </details>
2. $0 \le y - x$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $x \le y$
   </details>
3. $0 \le x + y$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le x$
   - $0 \le y$
   </details>
4. $\left(y - x\right) \left(x + y\right) \ge 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le x$
   - $x \le y$
   </details>
5. $x x \le y y$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $\left(y - x\right) \left(x + y\right) \ge 0$
   </details>

# Powers of two by induction

WTS $2^{n} \ge n + 1$ by induction on $n$

<details>
<summary>✅ likely</summary>

The induction base and step were validated up to a maximum dimension of 2.
</details>

1. WTS $2^{0} \ge 0 + 1$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

   1. $2^{0} \ge 0 + 1$

      <details>
      <summary>✅ verified</summary>

      No premises seemed necessary to show this.
      </details>
2. Given:

   - $2^{n} \ge n + 1$

   WTS $2^{n + 1} \ge n + 1 + 1$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

   1. $2 2^{n} \ge 2 \left(n + 1\right)$

      <details>
      <summary>✅ likely</summary>

      No counterexamples found up to a maximum dimension of 2.

      No premises seemed necessary to show this.
      </details>
   2. $2 \left(n + 1\right) \ge n + 1 + 1$

      <details>
      <summary>✅ likely</summary>

      No counterexamples found up to a maximum dimension of 2.

      No premises seemed necessary to show this.
      </details>
   3. $2^{n + 1} \ge n + 1 + 1$

      <details>
      <summary>✅ likely</summary>

      No counterexamples found up to a maximum dimension of 2.

      No premises seemed necessary to show this.
      </details>

# Squared norm in every dimension

Given:

- $x \in \mathbb{R}^{n}$

WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$ by induction on $n$

<details>
<summary>✅ likely</summary>

The induction base and step were validated up to a maximum dimension of 2.
</details>

1. Given:

   - $x \in \mathbb{R}^{1}$

   WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. Given:

   - $\forall x \in \mathbb{R}^{n}, \left\lVert x \right\rVert_{2}^{2} \ge 0$
   - $x \in \mathbb{R}^{n + 1}$

   WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Quantified claims as ordinary steps

Given:

- $y \in \mathbb{R}$
- $1 > 0$
- $1 < y$

WTS $\forall x \in \mathbb{R}, x x \ge 0$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $\forall x \in \mathbb{R}, x x \ge 0$
</details>

1. $\exists z > 0, z < y$

   <details>
   <summary>✅ witness found</summary>

   Witness:

   - $z = 1$

   Matched facts:

   - $1 > 0$
   - $1 < y$
   </details>
2. $\forall x \in \mathbb{R}, x x \ge 0$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>

# Existential evidence from direct subgoals

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

<details>
<summary>✅ witness found</summary>

Witness:

- $x = 1$

Matched facts:

- $1 > 0$
- $1 < y$
</details>

1. WTS $1 > 0$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. WTS $1 < y$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $1 < y$
   </details>

# Existential involving inferred dimensions

Given:

- $A \in \mathbb{R}^{n \times n}$
- $A B = I$

WTS $\exists C, C A = I$

<details>
<summary>✅ witness found</summary>

Witness:

- $C = B$

Matched facts:

- $B A = I$
</details>

1. $B A = I$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   This may follow from the following facts:

   - $A B = I$
   </details>
2. $\exists C, C A = I$

   <details>
   <summary>✅ witness found</summary>

   Witness:

   - $C = B$

   Matched facts:

   - $B A = I$
   </details>

# Determinant of a diagonal matrix

Given:

- $z \in \operatorname{Seq}_{n}(\mathbb{R})$

WTS $\det(\operatorname{diag}(z)) = \prod_{i=1}^{n}z_{i}$

<details>
<summary>✅ likely</summary>

No counterexamples found up to a maximum dimension of 2.

No premises seemed necessary to show this.
</details>

# Sum of the first naturals by induction

WTS $2 \sum_{i=1}^{n}i = n \left(n + 1\right)$ by induction on $n$

<details>
<summary>✅ likely</summary>

The induction base and step were validated up to a maximum dimension of 2.
</details>

1. WTS $2 \sum_{i=1}^{1}i = 1 \left(1 + 1\right)$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. Given:

   - $2 \sum_{i=1}^{n}i = n \left(n + 1\right)$

   WTS $2 \sum_{i=1}^{n + 1}i = \left(n + 1\right) \left(n + 1 + 1\right)$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Diagonal mapped square roots

Given:

- $\lambda \in \operatorname{Seq}_{2}(\mathbb{R})$
- $\lambda_{1} \ge 0$
- $\lambda_{2} \ge 0$

WTS $\operatorname{diag}(\operatorname{map}_{i=1}^{2}\lambda_{i}^{\frac{1}{2}}) \operatorname{diag}(\operatorname{map}_{i=1}^{2}\lambda_{i}^{\frac{1}{2}}) = \operatorname{diag}(\lambda)$

<details>
<summary>✅ verified</summary>

No premises seemed necessary to show this.
</details>
