# General endpoint leading-gauge foundation

The frozen foundation for the accepted P0174 `ENDPOINT_LEADING_GLOBAL.md`
and `ENDPOINT_SATURATED_STABILITY.md` consists of `LeadingKernel`,
`LeadingBounds`, and `LeadingRows` under `DR/Endpoint/`.

The actual polynomial kernel is
`B_ii = 1`, `B_ij = 1 - (m-2)! prod_{a outside {i,j}} r_a`.
Its row conjugacy holds with signed or zero row coordinates. Finite
Cauchy--Schwarz proves positive definiteness under the explicit marginal
criterion `(m-1)(sum r_i² + (m-2)! prod r_i) < 1`, with positive mass-one
rows. This is not an unconditional PSD claim: a persistent five-row
counterexample has positive mass-one marginals and quadratic value
`-3/80` on an explicit signed vector.

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

The pending step is the actual constrained minimum of the gauge minus a
row penalty, followed by the sharp scalar row-spread analysis and the
contender concentration bootstrap. No upper endpoint strip is claimed by
these foundations.

Verification: `lake --wfail build Test.EndpointLeadingRows
Test.EndpointLeadingKernel Test.EndpointLeadingBounds` passed 2,433 jobs,
22 persistent examples and 18 standard-only axiom audits, without warnings.
Controls include the indefinite positive kernel, the exact `2/9`
complementary-product endpoint and `8/45` diagonal defect, selected-factor
AM--GM with a signed unselected coordinate, zero columns, empty domains,
and a nonstationary row variation with exact derivative `43/36`.
