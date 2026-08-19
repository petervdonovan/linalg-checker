# Symbolic dimensions

## Assumptions

- $A \in \mathbb{R}^{n \times d + p}$
- $n = 2$
- $d = 1$
- $p = 1$

## Sentences

- $A = \begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix}$
- $d = 1$
- $n = 2$
- $p = 1$

# Independent implicit matrix constants

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}$
- $C \in \mathbb{R}^{2 \times 2}$
- $D \in \mathbb{R}^{2}$

## Sentences

- $A = I$
- $B = I$
- $C = \mathbb{0}$
- $D = \mathbb{0}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$
- $B = 1$
- $C = \begin{bmatrix}0 & 0 \\ 0 & 0\end{bmatrix}$
- $D = \begin{bmatrix}0 \\ 0\end{bmatrix}$

# Inferred matrix compatibility

## Assumptions

- $A B = C$
- $A \in \mathbb{R}^{2 \times 2}$
- $C \in \mathbb{R}^{2}$

## Sentences

- $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$
- $B = \begin{bmatrix}3 \\ 4\end{bmatrix}$
- $C = \begin{bmatrix}3 \\ 4\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$
- $B = \begin{bmatrix}3 \\ 4\end{bmatrix}$
- $C = \begin{bmatrix}3 \\ 4\end{bmatrix}$

# Impossible shape

## Assumptions

- $A \in \mathbb{R}^{n}$
- $n = 0$

## Sentences

## Conclusion

Unsat

# No small model

## Assumptions

- $A = A$
- $a \in \mathbb{R}$

## Sentences

- $a = 0$
- $a = 1$

## Conclusion

Unsat up to dimension 2

# Negative sum of squared vector norms

## Assumptions

- $\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})$

## Sentences

- $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} < 0$

## Conclusion

Unsat up to dimension 2

# Zero trace does not imply singularity

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Sentences

- $\operatorname{tr}(A) = 0$
- $\det(A) = 1$

## Conclusion

Model

- $A = \begin{bmatrix}0 & -1 \\ 1 & 0\end{bmatrix}$

# Cyclic trace

## Assumptions

- $A \in \mathbb{R}^{2}$
- $B \in \mathbb{R}^{1 \times 2}$

## Sentences

- $\operatorname{tr}(A B) \ne \operatorname{tr}(B A)$

## Conclusion

Unsat up to dimension 2

# Determinant multiplicativity

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$

## Sentences

- $\det(A B) \ne \det(A) \det(B)$

## Conclusion

Unsat up to dimension 2

# Defined scalar square root

## Assumptions

- $x \in \mathbb{R}$
- $x \ge 0$

## Sentences

- $x^{\frac{1}{2}} = 2$

## Conclusion

Model

- $x = 4$

# Potentially undefined scalar square root

## Assumptions

- $x \in \mathbb{R}$

## Sentences

- $x^{\frac{1}{2}} = x^{\frac{1}{2}}$

## Conclusion

Model

- $x = 0$

### Warnings

The expression $x^{\frac{1}{2}}$ may be undefined. For example:

- $x = -1$

# Assumed matrix square root

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$

## Sentences

- $A^{\frac{1}{2}} = A^{\frac{1}{2}}$

## Conclusion

Model

- $A = \begin{bmatrix}0 & 0 \\ 0 & 0\end{bmatrix}$

### Warnings

The existence of $A^{\frac{1}{2}}$ was assumed without checking.

# Negative squared two-norm

## Assumptions

- $v \in \mathbb{R}^{2}$

## Sentences

- $\left\lVert v \right\rVert_{2}^{2} < 0$

## Conclusion

Unsat up to dimension 2

# Negative two-norm

## Assumptions

- $v \in \mathbb{R}^{2}$

## Sentences

- $\left\lVert v \right\rVert_{2} < 0$

## Conclusion

Unsat up to dimension 2

# Bordered block matrix

## Assumptions

- $A \in \mathbb{R}^{2 \times 2}$
- $b \in \mathbb{R}^{2}$
- $c \in \mathbb{R}^{2}$
- $d \in \mathbb{R}$

## Sentences

- $\begin{bmatrix}A & b \\ c^\top & d\end{bmatrix} = \begin{bmatrix}1 & 2 & 3 \\ 4 & 5 & 6 \\ 7 & 8 & 9\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 2 \\ 4 & 5\end{bmatrix}$
- $b = \begin{bmatrix}3 \\ 6\end{bmatrix}$
- $c = \begin{bmatrix}7 \\ 8\end{bmatrix}$
- $d = 9$
