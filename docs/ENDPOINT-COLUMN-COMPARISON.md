# Quantitative column failure comparison

For `m≥2`, any positive label count `n`, and every nonnegative mass-one
vector `c` with `c_j≤C`, `endpoint_column_failure_comparison` proves

```
q_col(c) − q_col(U_n) ≥ choose(m,2) (1−b*C) V_c,
b = (m−2)(m+1)/2,   V_c = sum_j (c_j−1/n)^2.
```

The coefficient may be negative. Individual coordinates may be zero.
The theorem even retains `m>n`; the useful endpoint application later
uses `n≥m` and a sufficiently small cap.

`ColumnDeletionLower` proves the exact coefficient bound after two labels
are removed. Its ordered-injection recurrence gives
`k! e_k(c excluding a,b)≥1−k(k+3)C/2`. The prefix injection mass is at most
one, and each extension loses at most `(k+2)C`. This includes order zero
and empty or zero-coordinate outcome spaces.

`ColumnAveraging` supplies a finite version of the radial Schur comparison
from P0174 `ENDPOINT_POLYNOMIAL_STRIPS.md`. On the capped closed simplex,
minimize the adjusted column-failure objective, then minimize squared norm
within its compact minimum set. Every pair midpoint remains feasible and
does not increase the objective. Unequal coordinates would strictly lower
the second minimum, so the selected vector must be uniform. This handles
ties without assuming strict objective curvature.

`ColumnFailureComparison` supplies the actual midpoint inequality from
the proved two-column elementary expansion and the coefficient lower bound.
It identifies the uniform objective with the literal falling factorial,
and obtains the displayed quantitative inequality. No P2 maximizer or
gauge estimate is assumed.

`lake --wfail build Test.EndpointColumnComparison` passed 3,246 jobs, nine
examples and seven standard-only axiom audits. Controls include an empty
outcome space at order zero, zero coordinates, exact norm loss, a constant
objective with only ties, failure without midpoint monotonicity, the sharp
order-two boundary, `m>n` with a negative coefficient, and an empty capped
simplex. Warnings are rejected.
