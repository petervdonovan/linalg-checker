# Scalar argument

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. $x = x$
2. $x = 0$

# Matrix argument

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

1. $A = A$

# Sequence norm sum

Given:

- $\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})$

WTS $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$

1. $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} \ge 0$

# Negating an inequality

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $x < y$

WTS $-x > -y$

1. $-x < -y$

# Independent implicit matrix constants

WTS $\mathbb{0} = \begin{bmatrix}0 \\ 0\end{bmatrix}$

1. $I = \begin{bmatrix}1\end{bmatrix}$
2. $I = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$
3. $\mathbb{0} = \begin{bmatrix}0 & 0\end{bmatrix}$

# One-sided orthogonality

Given:

- $U^\top U = I$

WTS $U U^\top = I$

# Logic-chain preprocessing

Given:

- $x \in \mathbb{R}$
- $x = 0$

WTS $x = 0 \iff x \le 0 \implies x = x$

# Scalar square roots

Given:

- $x \in \mathbb{R}$
- $x \ge 0$

WTS $x^{\frac{1}{2}} \ge 0$

# Potentially undefined square root

Given:

- $x \in \mathbb{R}$

WTS $x^{\frac{1}{2}} = x^{\frac{1}{2}}$

# Assumed matrix square root

Given:

- $A \in \mathbb{R}^{2 \times 2}$

WTS $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

# Dimensionally invalid matrix square root

Given:

- $A \in \mathbb{R}^{2}$

WTS $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

# Vector two-norm

Given:

- $v \in \mathbb{R}^{2}$

WTS $\left\lVert v \right\rVert_{2} \ge 0$

# Wide matrix two-norm

Given:

- $A \in \mathbb{R}^{1 \times 2}$

WTS $\left\lVert A \right\rVert_{2} \ge 0$

1. $\left\lVert A \right\rVert_{2}^{2} \ge 0$

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

# Block selector identity

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$

WTS $\begin{bmatrix}A & B\end{bmatrix} \begin{bmatrix}I \\ \mathbb{0}\end{bmatrix} = A$

# Nested error localization

Given:

- $x \in \mathbb{R}$

WTS $x = x$

1. WTS $x = x$

   1. $x = 0$
   2. $x = x$
2. $x = x$

# Local givens and sibling names

WTS $0 = 0$

1. Given:

   - $y \in \mathbb{R}$

   WTS $y = 0$
2. Given:

   - $y \in \mathbb{R}$

   WTS $y = y$

# Squaring nonnegative reals

Given:

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $0 \le x$
- $x \le y$

WTS $x x \le y y$

1. WTS $0 \le y$

   1. $x \le y$
   2. $0 \le y$
2. $0 \le y - x$
3. $0 \le x + y$
4. $\left(y - x\right) \left(x + y\right) \ge 0$
5. $x x \le y y$

# Powers of two by induction

WTS $2^{n} \ge n + 1$ by induction on $n$

1. WTS $2^{0} \ge 0 + 1$

   1. $2^{0} \ge 0 + 1$
2. Given:

   - $2^{n} \ge n + 1$

   WTS $2^{n + 1} \ge n + 1 + 1$

   1. $2 2^{n} \ge 2 \left(n + 1\right)$
   2. $2 \left(n + 1\right) \ge n + 1 + 1$
   3. $2^{n + 1} \ge n + 1 + 1$

# Squared norm in every dimension

Given:

- $x \in \mathbb{R}^{n}$

WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$ by induction on $n$

1. Given:

   - $x \in \mathbb{R}^{1}$

   WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$
2. Given:

   - $\forall x \in \mathbb{R}^{n}, \left\lVert x \right\rVert_{2}^{2} \ge 0$
   - $x \in \mathbb{R}^{n + 1}$

   WTS $\left\lVert x \right\rVert_{2}^{2} \ge 0$

# Quantified claims as ordinary steps

Given:

- $y \in \mathbb{R}$
- $1 > 0$
- $1 < y$

WTS $\forall x \in \mathbb{R}, x x \ge 0$

1. $\exists z > 0, z < y$
2. $\forall x \in \mathbb{R}, x x \ge 0$

# Existential evidence from direct subgoals

Given:

- $y \in \mathbb{R}$
- $1 < y$

WTS $\exists x > 0, x < y$

1. WTS $1 > 0$
2. WTS $1 < y$

# Existential involving inferred dimensions

Given:

- $A \in \mathbb{R}^{n \times n}$
- $A B = I$

WTS $\exists C, C A = I$

1. $B A = I$
2. $\exists C, C A = I$

# Determinant of a diagonal matrix

Given:

- $z \in \operatorname{Seq}_{n}(\mathbb{R})$

WTS $\det(\operatorname{diag}(z)) = \prod_{i=1}^{n}z_{i}$

# Sum of the first naturals by induction

WTS $2 \sum_{i=1}^{n}i = n \left(n + 1\right)$ by induction on $n$

1. WTS $2 \sum_{i=1}^{1}i = 1 \left(1 + 1\right)$
2. Given:

   - $2 \sum_{i=1}^{n}i = n \left(n + 1\right)$

   WTS $2 \sum_{i=1}^{n + 1}i = \left(n + 1\right) \left(n + 1 + 1\right)$

# Diagonal mapped square roots

Given:

- $\lambda \in \operatorname{Seq}_{2}(\mathbb{R})$
- $\lambda_{1} \ge 0$
- $\lambda_{2} \ge 0$

WTS $\operatorname{diag}(\operatorname{map}_{i=1}^{2}\lambda_{i}^{\frac{1}{2}}) \operatorname{diag}(\operatorname{map}_{i=1}^{2}\lambda_{i}^{\frac{1}{2}}) = \operatorname{diag}(\lambda)$
