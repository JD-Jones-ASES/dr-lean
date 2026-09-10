# Quantitative column failure comparison

For `m≥2`, any positive label count `n`, and every nonnegative mass-one
vector `c` with `c_j≤C`, let q_col(c) be the probability of a collision
among m independent draws from c. Then `endpoint_column_failure_comparison` proves

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

A finite midpoint argument proves the comparison. On the capped closed
simplex, minimize the adjusted column-failure objective, then minimize
squared norm among its minimizers. Every pair midpoint remains feasible
and does not increase the objective. Unequal coordinates would strictly
lower the second minimum, so the selected vector is uniform. This also
handles ties when the objective itself is not strictly convex.

`ColumnFailureComparison` supplies the actual midpoint inequality from
the proved two-column elementary expansion and the coefficient lower bound.
It identifies the uniform objective with the literal falling factorial,
and obtains the displayed quantitative inequality. No P2 maximizer or
gauge estimate is assumed.

## Formal statements

[ColumnDeletionLower](../DR/Endpoint/ColumnDeletionLower.lean), [ColumnAveraging](../DR/Endpoint/ColumnAveraging.lean), [ColumnFailureComparison](../DR/Endpoint/ColumnFailureComparison.lean).
