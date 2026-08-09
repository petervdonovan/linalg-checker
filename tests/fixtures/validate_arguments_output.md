# Scalar argument

## Assumptions

- $x \in \mathbb{R}$

## Steps

1. $x = x$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No tracked premises appeared in the unsatisfiable cores.
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

   No tracked premises appeared in the unsatisfiable cores.
   </details>

# Matrix argument

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Steps

1. $A = A$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No tracked premises appeared in the unsatisfiable cores.
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

   No tracked premises appeared in the unsatisfiable cores.
   </details>
2. $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} = 0$ is satisfied by:

   - $d = 1$
   - $n = 1$
   - $\vec{z}_{1} = \begin{bmatrix}-1\end{bmatrix}$
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

   - $x = 0$
   - $y = \frac{1}{2}$
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

   No tracked premises appeared in the unsatisfiable cores.
   </details>
2. $I = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No tracked premises appeared in the unsatisfiable cores.
   </details>
3. $\mathbb{0} = \begin{bmatrix}0 & 0\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No tracked premises appeared in the unsatisfiable cores.
   </details>
4. $\mathbb{0} = \begin{bmatrix}0 \\ 0\end{bmatrix}$

   <details>
   <summary>✅ likely</summary>

   No counterexamples found up to a maximum dimension of 2.

   No tracked premises appeared in the unsatisfiable cores.
   </details>

# One-sided orthogonality

## Assumptions

- $U \in \mathbb{R}^{2}$
- $U = \begin{bmatrix}1 \\ 0\end{bmatrix}$
- $U^\top U = I$

## Steps

1. $U U^\top = I$

   <details>
   <summary>❌ counterexample found</summary>

   The negation of $U U^\top = I$ is satisfied by:

   - $U = \begin{bmatrix}1 \\ 0\end{bmatrix}$
   </details>
