# Actual collision-cluster criterion

`DR/Endpoint/RowCollisionCluster.lean` proves the collision-cluster estimate
from the Lab's P0174 `ENDPOINT_COLLISION_CLUSTER_STRIPS.md`, section 4,
for the actual independent, nonidentically distributed row law. If `L` is
the two-row deletion matrix and `D` the expected number of colliding pairs,
then, for every real vector `x`,

```
(1 - 3D) sum_i x_i² - (sum_i x_i)² <= -xᵀ E[L] x.
```

The proof uses the already formalized exhaustive assignment classification:
no collisions, one doubleton, one triple, two doubletons, or zero deletion
matrix. The exact intermediate coefficient is `3 p_avoid - 2`; the union
bound `1 - p_avoid <= D` gives the displayed result. Each row is normalized;
zero cells are allowed. There is no small-intensity hypothesis in this
expectation theorem, and empty row sets are included.

`DR/Endpoint/RowClusterKernel.lean` transfers the estimate to the actual
endpoint averaging kernel. Writing `s_i = r_i/h` and `G = (prod_i r_i)/h²`,
positive row masses and a positive scale `h` give a sufficient criterion:

```
sum_i (1 - m s_i)² <= 1/9,
D(normalizeRows P) <= 1/12,
E >= 2 m² G.
```

The resulting bound is `xᵀ diag(s) C diag(s) x >= (19/36) G sum_i x_i²`.
This uses a direct finite Cauchy estimate
`(sum x)² <= 2m²(sum s_i x_i)² + (2/9)sum x_i²`; it avoids a matrix inverse
and is sufficient under the accepted long-strip estimates. The invertible
row congruence proves positive definiteness on all real vectors. Neither
original-row avoidance nor deleted-row avoidance is substituted for the
expected collision count of this actual board.

This is a conditional matrix input, not a long-strip principal theorem.
The missing upstream work is the general endpoint leading gauge, its
quantitative/saturated stability, and the actual contender concentration
bootstrap. In particular, `c_max < 25/N` is not a premise silently obtained
from the existing transition theorem.

Run `lake --wfail build Test.RowCollisionCluster`. Controls include an
actual injective assignment showing that the all-ones term cannot be
dropped, an irreparable four-row class, arbitrary signed test vectors,
the empty domain, both closed scalar thresholds, zero vectors, and failed
claims when any scalar criterion is removed. Seven dependency audits are
restricted to the standard Lean axioms.
