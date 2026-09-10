# Actual collision-cluster criterion

Let each row independently choose one column according to a possibly
different normalized distribution. For an assignment z, define L(z) to
have zero diagonal and L(z)_{ih}=1 exactly when deleting distinct rows
i,h leaves an injective column assignment. If D is the expected number
of colliding unordered pairs, then every real vector x satisfies

```
(1 - 3D) sum_i x_i² - (sum_i x_i)² <= -xᵀ E[L] x.
```

The proof uses the exhaustive assignment classification:
no collisions, one doubleton, one triple, two doubletons, or zero deletion
matrix. The exact intermediate coefficient is `3 p_avoid - 2`; the union
bound `1 - p_avoid <= D` gives the displayed result. Each row is normalized;
zero cells are allowed. There is no small-intensity hypothesis in this
expectation theorem, and empty row sets are included.

`DR/Endpoint/RowClusterKernel.lean` transfers the estimate to the actual
endpoint averaging kernel. Writing `s_i = r_i/h` and `G = (prod_i r_i)/h²`,
positive row masses and a positive scale `h` give a sufficient criterion
for C=averagingKernel P (m−2), with E=e_(m−2)(colSum P):

```
sum_i (1 - m s_i)² <= 1/9,
D(normalizeRows P) <= 1/12,
E >= 2 m² G.
```

The resulting bound is `xᵀ diag(s) C diag(s) x >= (19/36) G sum_i x_i²`.
This uses a direct finite Cauchy estimate
`(sum x)² <= 2m²(sum s_i x_i)² + (2/9)sum x_i²`; it avoids a matrix inverse
and is sufficient under the stated long-strip estimates. The invertible
row congruence proves positive definiteness on all real vectors. Neither
original-row avoidance nor deleted-row avoidance is substituted for the
expected collision count of this actual board.

For endpoint contenders in the [quadratic strip](ENDPOINT-QUADRATIC.md),
leading-gauge stability gives the row concentration and column cap needed
by this criterion after two columns are deleted. The
[combined strip](ENDPOINT-COMBINED.md) uses a stronger elementary
coefficient estimate to apply the same argument for m≥5.

## Formal statements

[RowCollisionCluster](../DR/Endpoint/RowCollisionCluster.lean), [RowClusterKernel](../DR/Endpoint/RowClusterKernel.lean).
