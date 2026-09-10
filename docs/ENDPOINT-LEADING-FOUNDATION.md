# General endpoint leading-gauge foundation

The leading gauge is built from a complementary-product matrix on the
row marginals. Its entries are polynomial, so its identities remain valid
when some row masses vanish. Positive definiteness, when needed, follows
from an explicit row-spread inequality rather than the definition.

The actual polynomial kernel is
`B_ii = 1`, `B_ij = 1 - (m-2)! prod_{a outside {i,j}} r_a`.
Its row conjugacy holds with signed or zero row coordinates. Finite
Cauchy--Schwarz proves positive definiteness under the explicit marginal
criterion `(m-1)(sum r_i² + (m-2)! prod r_i) < 1`, with positive mass-one
rows. The condition is needed: B need not be positive semidefinite
for arbitrary positive mass-one row marginals.

For all nonnegative mass-one row marginals and nonnegative column vectors,
AM--GM bounds each complementary product by `a_(m-2)` and gives the actual
cost inequalities

```
c²(1 - beta) <= vᵀBv <= c²,
beta = a_(m-2)(1 - 1/m).
```

For every `m >= 3`, `0 <= beta < 1`. Thus each nonempty column has strictly
positive square-root cost; a cost vanishes exactly when the actual column
mass vanishes. These statements retain zero rows, cells and columns.

The row-scaling board is `endpointRowBoard r X`, with entries `r_i X_ij`.
For a fixed row-normalized law `X`, the signed polynomial identity is

```
h_j² = (sum_i r_i X_ij)² - gamma T_j,
gamma = (m-2)! prod_i r_i,
T_j = (sum_i X_ij)² - sum_i X_ij².
```

The formal derivative along `r + t w` is
`2 c_j sum_i w_i X_ij - gamma T_j sum_i w_i/r_i` when all rows are nonzero.
The square-root derivative is proved where the actual polynomial is
positive. Empty columns stay identically zero for every real row scaling.
There is no stationarity premise or inference in this derivative package.
Its only imported square helper is the general finite-product derivative
from `Square/Stationarity`; it does not use a Dittert maximization theorem.

The [stationarity argument](ENDPOINT-LEADING-STATIONARITY.md) applies
these derivatives at a compact minimum of the gauge minus a row penalty.
The [coarse](ENDPOINT-COARSE-GAUGE.md) and
[saturated](ENDPOINT-SATURATED-GAUGE.md) estimates then prove the
row-spread criterion at that minimum and transfer its value to every board.

## Formal statements

[LeadingKernel](../DR/Endpoint/LeadingKernel.lean), [LeadingBounds](../DR/Endpoint/LeadingBounds.lean), [LeadingRows](../DR/Endpoint/LeadingRows.lean).
