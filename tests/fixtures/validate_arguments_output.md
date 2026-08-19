# Scalar argument

## Assumptions

- $x \in \mathbb{R}$

## Steps

1. $x = x$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
2. $x = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $x = 0$ is satisfied by:

   - $x = 2$
   </details>
3. $x = x$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Matrix argument

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Steps

1. $A = A$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
2. $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$ is satisfied by:

   - $A = \begin{bmatrix}\square & \square \\ \square & 2\end{bmatrix}$
   </details>

# Sequence norm sum

## Assumptions

- $\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})$

## Steps

1. $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} \ge 0$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
2. $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$ is satisfied by:

   - $d = 1$
   - $n = 1$
   - $\vec{z}_{1} = \begin{bmatrix}2\end{bmatrix}$
   </details>

# Negating an inequality

## Assumptions

- $x \in \mathbb{R}$
- $y \in \mathbb{R}$
- $x < y$

## Steps

1. $-x < -y$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $-x < -y$ is satisfied by:

   - $x = \frac{-1}{2}$
   - $y = 0$
   </details>
2. $-x > -y$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   This may follow from the following facts:

   - $x < y$
   </details>

# Independent implicit matrix constants

## Assumptions

## Steps

1. $I = \begin{bmatrix}1\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
2. $I = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
3. $\mathbb{0} = \begin{bmatrix}0 & 0\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
4. $\mathbb{0} = \begin{bmatrix}0 \\ 0\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# One-sided orthogonality

## Assumptions

- $U^\top U = I$

## Steps

1. $U U^\top = I$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $U U^\top = I$ is satisfied by:

   - $U = \begin{bmatrix}\frac{-3}{4} \\ -\left(\frac{7}{16}\right)^{\frac{1}{2}}\end{bmatrix}$
   </details>

# Logic-chain preprocessing

## Assumptions

- $x \in \mathbb{R}$
- $x = 0$

## Steps

1. $x = 0 \iff x \le 0 \implies x = x$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   This may follow from the following facts:

   - $x = 0$
   </details>

# Scalar square roots

## Assumptions

- $x \in \mathbb{R}$
- $x \ge 0$

## Steps

1. $x^{\frac{1}{2}} \ge 0$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Potentially undefined square root

## Assumptions

- $x \in \mathbb{R}$

## Steps

1. $x^{\frac{1}{2}} = x^{\frac{1}{2}}$

   <details>
   <summary>⚠️ conditional</summary>

   The expression $x^{\frac{1}{2}}$ may be undefined. For example:

   - $x = -1$
   </details>

# Assumed matrix square root

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Steps

1. $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

   <details>
   <summary>⚠️ conditional</summary>

   The existence of $A^{\frac{1}{2}}$ was assumed without checking.
   </details>

# Dimensionally invalid matrix square root

## Assumptions

- $A \in \mathbb{R}^{2}$

## Steps

1. $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

   <details>
   <summary>⚠️ dimensionally invalid</summary>

   This step is not dimensionally meaningful in the following environment:

   - $A \in \mathbb{R}^{2}$
   </details>

# Vector two-norm

## Assumptions

- $v \in \mathbb{R}^{2}$

## Steps

1. $\left\lVert v \right\rVert_{2} \ge 0$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Wide matrix two-norm

## Assumptions

- $A \in \mathbb{R}^{1 \times 2}$

## Steps

1. $\left\lVert A \right\rVert_{2}^{2} \ge 0$

   <details>
   <summary>⚠️ dimensionally invalid</summary>

   This step is not dimensionally meaningful in the following environment:

   - $A \in \mathbb{R}^{1 \times 2}$
   </details>
2. $\left\lVert A \right\rVert_{2} \ge 0$

   <details>
   <summary>⚠️ dimensionally invalid</summary>

   This step is not dimensionally meaningful in the following environment:

   - $A \in \mathbb{R}^{1 \times 2}$
   </details>

# Block multiplication formula

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$
- $C \in \mathbb{R}^{2 \times 2}$
- $D \in \mathbb{R}^{2 \times 2}$
- $E \in \mathbb{R}^{2 \times 2}$
- $F \in \mathbb{R}^{2 \times 2}$
- $G \in \mathbb{R}^{2 \times 2}$
- $H \in \mathbb{R}^{2 \times 2}$

## Steps

1. $\begin{bmatrix}A & B \\ C & D\end{bmatrix} \begin{bmatrix}E & F \\ G & H\end{bmatrix} = \begin{bmatrix}A E + B G & A F + B H \\ C E + D G & C F + D H\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>

# Block selector identity

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$

## Steps

1. $\begin{bmatrix}A & B\end{bmatrix} \begin{bmatrix}I \\ \mathbb{0}\end{bmatrix} = A$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No premises seemed necessary to show this.
   </details>
