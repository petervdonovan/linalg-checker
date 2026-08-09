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

Unsat up to dimension 3

# Negative sum of squared vector norms

## Assumptions

- $\vec{z} \in \operatorname{Seq}_{n}(\mathbb{R}^{d})$

## Sentences

- $\sum_{i=1}^{n}\vec{z}_{i}^\top \vec{z}_{i} < 0$

## Conclusion

Unsat up to dimension 3
