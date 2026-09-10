# Closing endpoint averaging from equal columns

[ColumnRigidity](../DR/Endpoint/ColumnRigidity.lean) proves a general closure
step for sample size m. It assumes m≥2 and n>0. If every global maximizer
on the m×n probability simplex has equal columns, then the uniform matrix
is the unique global maximizer. The theorem needs no corresponding
rigidity statement on the transposed board.

Write r_i for the row masses, a=m!/m^m, b=(n)_m/n^m and
R=m^m product(r_i). Equal columns give P_ij=r_i/n. Directly evaluating
the three embedding sums in the inclusive-OR identity gives

```
F(P) = a R + b - a R b.
F(U) = a   + b - a b.
```

On the closed probability simplex, R≤1, with equality exactly when all
row masses equal 1/m. Since a>0 and b<1, an equal-column board with
F(P)≥F(U) must have R=1, hence every cell equals 1/(mn). Compactness
then converts the assumed global-maximizer column rigidity into the
sharp bound and its complete equality case.

The general closure theorem is
`uniform_maximizer_endpoint_of_column_rigidity`. Its premise is supplied
by strict midpoint averaging whenever every retained two-column kernel
is positive definite; see [kernel closure](../DR/Endpoint/EndpointKernelClosure.lean).

The proof also covers n<m and n=1. The restriction m≥2 is necessary
for unique equality: with one sampled cell, the separation probability is
one for every probability board.

## Formal statements

[ColumnRigidity](../DR/Endpoint/ColumnRigidity.lean).
