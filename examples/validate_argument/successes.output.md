# Squaring nonnegative numbers is monotone

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $0 \le x$
- $x \le y$

WTS $x^{2} \le y^{2}$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $x^{2} \le y^{2}$
</details>

1. $0 \le y$

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
3. $0 \le \left(y - x\right) \left(x + y\right)$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le x$
   - $x \le y$
   </details>
4. $0 \le y^{2} - x^{2}$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le \left(y - x\right) \left(x + y\right)$
   </details>
5. $x^{2} \le y^{2}$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le \left(y - x\right) \left(x + y\right)$
   </details>

# A sum of symmetric matrices is symmetric

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$
- $A^\top = A$
- $B^\top = B$

WTS $\left(A + B\right)^\top = A + B$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $B^\top = B$
- $A^\top + B^\top = A + B$
</details>

1. $\left(A + B\right)^\top = A^\top + B^\top$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. $A^\top + B^\top = A + B$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $A^\top = A$
   - $B^\top = B$
   </details>
3. $\left(A + B\right)^\top = A + B$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $B^\top = B$
   - $A^\top + B^\top = A + B$
   </details>

# Orthogonal matrices preserve squared length

Given:

- $U \in \mathbb{R}^{n \times n}$
- $\vec{x} \in \mathbb{R}^{n}$
- $U^\top U = I$

WTS $\left\lVert U \vec{x} \right\rVert_{2}^{2} = \left\lVert \vec{x} \right\rVert_{2}^{2}$

<details>
<summary>✅ likely</summary>

No counterexamples found up to a maximum dimension of 2.

This may follow from the following facts:

- $U^\top U = I$
- $\vec{x}^\top U^\top U \vec{x} = \vec{x}^\top I \vec{x}$
</details>

1. $\left(U \vec{x}\right)^\top U \vec{x} = \vec{x}^\top U^\top U \vec{x}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
2. $\vec{x}^\top U^\top U \vec{x} = \vec{x}^\top I \vec{x}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   This may follow from the following facts:

   - $U^\top U = I$
   </details>
3. $\vec{x}^\top I \vec{x} = \vec{x}^\top \vec{x}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Scalar multiples of null-space vectors remain in the null space

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\vec{x} \in \mathbb{R}^{2}$
- $c \in \mathbb{R}$
- $\vec{x} \in \operatorname{Nul}(A)$

WTS $c \vec{x} \in \operatorname{Nul}(A)$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $A c \vec{x} = \mathbb{0}$
</details>

1. $A \vec{x} = \mathbb{0}$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $\vec{x} \in \operatorname{Nul}(A)$
   </details>
2. $A c \vec{x} = c A \vec{x}$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
3. $A c \vec{x} = \mathbb{0}$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $\vec{x} \in \operatorname{Nul}(A)$
   </details>
4. $c \vec{x} \in \operatorname{Nul}(A)$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $A c \vec{x} = \mathbb{0}$
   </details>

# Linear combinations of range vectors remain in the range

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $\vec{x} \in \mathbb{R}^{2}$
- $\vec{y} \in \mathbb{R}^{2}$
- $a \in \mathbb{R}$
- $b \in \mathbb{R}$
- $\vec{x} \in \operatorname{Range}(A)$
- $\vec{y} \in \operatorname{Range}(A)$

WTS $a \vec{x} + b \vec{y} \in \operatorname{Range}(A)$

<details>
<summary>✅ witness found</summary>

Witness:

- $w_{preimage of A} = a \vec{u} + b \vec{v}$

Matched facts:

- $a \vec{x} + b \vec{y} = A \left(a \vec{u} + b \vec{v}\right)$
</details>

1. $\vec{x} = A \vec{u}$

   <details>
   <summary>✅ witness introduced</summary>

   From $\vec{x} \in \operatorname{Range}(A)$:

   - $\vec{u}$ as a witness for $w_{preimage of A}$
   </details>
2. $\vec{y} = A \vec{v}$

   <details>
   <summary>✅ witness introduced</summary>

   From $\vec{y} \in \operatorname{Range}(A)$:

   - $\vec{v}$ as a witness for $w_{preimage of A}$
   </details>
3. $a \vec{x} + b \vec{y} = A \left(a \vec{u} + b \vec{v}\right)$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $\vec{x} \in \operatorname{Range}(A)$
   - $\vec{y} \in \operatorname{Range}(A)$
   - $\vec{x} = A \vec{u}$
   - $\vec{y} = A \vec{v}$
   </details>
4. $a \vec{x} + b \vec{y} \in \operatorname{Range}(A)$

   <details>
   <summary>✅ witness found</summary>

   Witness:

   - $w_{preimage of A} = a \vec{u} + b \vec{v}$

   Matched facts:

   - $a \vec{x} + b \vec{y} = A \left(a \vec{u} + b \vec{v}\right)$
   </details>

# Powers of two by explicit induction obligations

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

# An existential claim established by direct subgoals

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

1. $1 > 0$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
2. $1 < y$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $1 < y$
   </details>

# A set-comprehension closure argument

Given:

- $y \in \left\{x \in \mathbb{R} : x > 0\right\}$

WTS $y + 1 \in \left\{x \in \mathbb{R} : x > 0\right\}$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $y + 1 > 0$
</details>

1. $y > 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $y \in \left\{x \in \mathbb{R} : x > 0\right\}$
   </details>
2. $y + 1 > 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $y \in \left\{x \in \mathbb{R} : x > 0\right\}$
   </details>
3. $y + 1 \in \left\{x \in \mathbb{R} : x > 0\right\}$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $y + 1 > 0$
   </details>

# A tempting but invalid zero-product cancellation

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $x y = 0$

WTS $x = 0$

<details>
<summary>❌ counterexample found</summary>

The negation of $x = 0$ is satisfied by:

- $x = -1$
- $y = 0$
</details>

1. $x y = 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $x y = 0$
   </details>
2. $x = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $x = 0$ is satisfied by:

   - $x = -1$
   - $y = 0$
   </details>

# Adding a nonnegative scalar preserves an upper bound

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $z \in \mathbb{R}$
- $x \le y$
- $0 \le z$

WTS $x \le y + z$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $x \le y + z$
</details>

1. $y \le y + z$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $0 \le z$
   </details>
2. $x \le y + z$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $x \le y$
   - $0 \le z$
   </details>

# A short implication chain from a zero hypothesis

Given:

- $x \in \mathbb{R}$
- $x = 0$

WTS $x = 0 \iff x \le 0 \implies x = x$

<details>
<summary>✅ verified</summary>

This follows from the following facts:

- $x = 0$
</details>

1. $x \le 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $x = 0$
   </details>
2. $x = 0 \iff x \le 0$

   <details>
   <summary>✅ verified</summary>

   This follows from the following facts:

   - $x = 0$
   </details>
3. $x = x$

   <details>
   <summary>✅ verified</summary>

   No premises seemed necessary to show this.
   </details>
