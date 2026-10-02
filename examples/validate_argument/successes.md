# Squaring nonnegative numbers is monotone

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $0 \le x$
- $x \le y$

WTS $x^2 \le y^2$

1. The lower bound on x and the comparison with y give $0 \le y$.
2. Rearranging the comparison gives $0 \le y - x$.
3. The two nonnegative factors give $0 \le \left(y - x\right) \left(x + y\right)$.
4. Expanding the product gives $0 \le y^2 - x^2$.
4. Thus, $x^2 \le y^2$.

# A sum of symmetric matrices is symmetric

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$
- $A^\top = A$
- $B^\top = B$

WTS $\left(A + B\right)^\top = A + B$

1. Transpose distributes over addition: $\left(A + B\right)^\top = A^\top + B^\top$.
2. Substitute the symmetry hypotheses: $A^\top + B^\top = A + B$.
3. Combining the two equalities proves $\left(A + B\right)^\top = A + B$.

# Orthogonal matrices preserve squared length

Given:

- $U \in \mathbb{R}^{n \times n}$
- $x \in \mathbb{R}^{n}$
- $U^\top U = I$

WTS $\left\lVert U x \right\rVert_{2}^2 = \left\lVert x \right\rVert_{2}^2$

1. Expand the transpose of the product: $\left(U x\right)^\top \left(U x\right) = x^\top U^\top U x$.
2. Use orthogonality in the middle: $x^\top U^\top U x = x^\top I x$.
3. The identity acts neutrally: $x^\top I x = x^\top x$.

# Scalar multiples of null-space vectors remain in the null space

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $x \in \mathbb{R}^{2}$
- $c \in \mathbb{R}$
- $x \in \operatorname{Nul}(A)$

WTS $c x \in \operatorname{Nul}(A)$

1. Null-space membership means the matrix kills the vector: $A x = \mathbb{0}$.
2. Pull the scalar through the matrix product: $A \left(c x\right) = c \left(A x\right)$.
3. Substitute the zero result: $A \left(c x\right) = \mathbb{0}$.
4. Therefore the scalar multiple is in the null space: $c x \in \operatorname{Nul}(A)$.

# Linear combinations of range vectors remain in the range

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $x \in \mathbb{R}^{2}$
- $y \in \mathbb{R}^{2}$
- $a \in \mathbb{R}$
- $b \in \mathbb{R}$
- $x \in \operatorname{Range}(A)$
- $y \in \operatorname{Range}(A)$

WTS $a x + b y \in \operatorname{Range}(A)$

1. Choose a preimage for the first range vector: $x = A u$.
2. Choose a preimage for the second range vector: $y = A v$.
3. Substitute both preimages and distribute: $a x + b y = A \left(a u + b v\right)$.
4. This is the definition of range membership: $a x + b y \in \operatorname{Range}(A)$.

# Powers of two by explicit induction obligations

WTS $2^{n} \ge n + 1$ by induction on $n$

1. WTS $2^{0} \ge 0 + 1$

   1. The base case is immediate: $2^{0} \ge 0 + 1$.
2. Given:

   - $2^{n} \ge n + 1$

   WTS $2^{n + 1} \ge n + 1 + 1$

   1. Doubling preserves the induction inequality: $2 2^{n} \ge 2 \left(n + 1\right)$.
   2. The doubled lower bound is large enough for the successor: $2 \left(n + 1\right) \ge n + 1 + 1$.
   3. Rewriting the left side as the next power gives $2^{n + 1} \ge n + 1 + 1$.

# An existential claim established by direct subgoals

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. The proposed witness is positive: $1 > 0$.
2. The proposed witness is below y: $1 < y$.

# A set-comprehension closure argument

Given:

- $y \in \left\{x \in \mathbb{R} : x > 0\right\}$

WTS $y + 1 \in \left\{x \in \mathbb{R} : x > 0\right\}$

1. Membership in the positive reals gives $y > 0$.
2. Adding one preserves positivity: $y + 1 > 0$.
3. Therefore $y + 1 \in \left\{x \in \mathbb{R} : x > 0\right\}$.

# A tempting but invalid zero-product cancellation

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $x y = 0$

WTS $x = 0$

1. The zero-product hypothesis is available: $x y = 0$.
2. Canceling the factor y would give $x = 0$.

# Adding a nonnegative scalar preserves an upper bound

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $z \in \mathbb{R}$
- $x \le y$
- $0 \le z$

WTS $x \le y + z$

1. Adding a nonnegative scalar raises the upper bound: $y \le y + z$.
2. Chaining the two inequalities gives $x \le y + z$.

# A short implication chain from a zero hypothesis

Given:

- $x \in \mathbb{R}$
- $x = 0$

WTS $x = 0 \iff x \le 0 \implies x = x$

1. The zero hypothesis implies the upper bound: $x \le 0$.
2. The hypothesis and its consequence give the biconditional: $x = 0 \iff x \le 0$.
3. Reflexivity supplies the final conclusion: $x = x$.
