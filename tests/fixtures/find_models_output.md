# Scalar values

## Environment

- $n \in \mathbb{Z}$
- $x \in \mathbb{R}$

## Sentences

- $n = -2$
- $2 x = 1$

## Conclusion

Model

- $n = -2$
- $x = \frac{1}{2}$

# Matrix value

## Environment

- $A \in \mathbb{R}^{2 \times 2}$

## Sentences

- $A = \begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 2 \\ 3 & 4\end{bmatrix}$

# Matrix value with many models

## Environment

- $A \in \mathbb{R}^{2 \times 2}$

## Sentences

- $A = A$

## Conclusion

Model

- $A = \begin{bmatrix}\square & \square \\ \square & \square\end{bmatrix}$

# Unconstrained scalar

## Environment

- $x \in \mathbb{R}$

## Sentences

- $x = x$

## Conclusion

Model

- $x = \square$

# Rectangular matrix scaling

## Environment

- $A \in \mathbb{R}^{2 \times 3}$

## Sentences

- $2 A = \begin{bmatrix}2 & 4 & 6 \\ 8 & 10 & 12\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}1 & 2 & 3 \\ 4 & 5 & 6\end{bmatrix}$

# Matrix factorization

## Environment

- $A \in \mathbb{R}^{2 \times 2}$
- $B \in \mathbb{R}^{2 \times 2}$

## Sentences

- $A B = \begin{bmatrix}1 & 0 \\ 0 & 1\end{bmatrix}$

## Conclusion

Model

- $A = \begin{bmatrix}\frac{1}{8} & \frac{-1}{2} \\ \frac{-15}{8} & \frac{-1}{2}\end{bmatrix}$
- $B = \begin{bmatrix}\frac{1}{2} & \frac{-1}{2} \\ \frac{-15}{8} & \frac{-1}{8}\end{bmatrix}$

# Inconsistent

## Environment

- $z \in \mathbb{Z}$

## Sentences

- $z < 0$
- $z > 0$

## Conclusion

Unsat
