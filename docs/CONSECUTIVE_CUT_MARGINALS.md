# Size-sensitive endpoint marginal bounds

The three `ConsecutiveCutGeometry`, `ConsecutiveCutMarginals`, and
`ConsecutiveCutShared` modules prove the analytic marginal estimates
needed by the finite consecutive active-cut argument. They operate on
actual rectangular endpoint contenders, with arbitrary zero entries.
The single remaining scalar input is the chosen normalized row cap `H`:

```
H ≥ 1,    m b/[2(1-b)] ≤ (H-1)^2,
```

where `b=distinctUniformProbability n m`. They do not assume the desired
subset bounds, a balanced dominating matrix, or the final endpoint
inequality. The finite range's common cap `H=101/100` is subsequently
checked by rational arithmetic.

## Exact coefficients

For an actual row subset of size `k` and column subset of size `l`, put

```
A_k = 2 H² k(m-k)/m³,
B_l = 2(n-1) l(n-l)/(n²m).
```

Writing `d_r=1-R`, `d_c=1-S`, and `delta=b-T` with the actual endpoint
normalizations, the modules prove

```
row_discrepancy² ≤ A_k d_r/(1-b),
column_discrepancy² ≤ B_l d_c/(1-b),
(|row_discrepancy|+|column_discrepancy|)²
  ≤ [A_k+(a/b)B_l] delta/(1-b).
```

The row cap comes from the already proved product-deficit singleton
bound. The scalar inequality
`(x-1)²/(2H²) ≤ x-1-log x` on `0<x≤H` is derived from the proved
inverse-variance log inequality, splitting at `x=1`. Summing and using
the actual product deficit proves the full row variance bound.

The column estimate uses the existing closed-simplex Maclaurin variance
theorem and the proved contender deficit bounds. The exact orthogonal
projection coefficient `k(d-k)/d` follows from a centered indicator and
Cauchy–Schwarz; empty/full subsets and signed total-one inputs remain
valid. A proved two-term weighted Cauchy inequality combines the two
estimates using their shared rook-deficit budget.

The source is the first-family marginal argument in the Lab's
`P0174_rybin_semimatchings/ACTIVE_CUT_RECTANGULAR_EXTENSIONS.md`. The
cut coefficient is exactly `[A_k+(a/b)B_l]/(k/m+l/n-1)²`. Its connection
to actual subsets retains a strictly positive cut demand. Finite cut
certificates and the permanent-floor contradiction remain separate
obligations beyond this analytic increment.

## Verification

Run `lake --wfail build Test.ConsecutiveCutMarginals`. Tests include both
sides of the logarithmic bound, the cap endpoint, signed projection,
empty/full subsets, zero axis coefficients, the actual 19×20 contender
with its cap discharged, and a false stronger projection coefficient.
Ten public axiom audits expose only the standard Lean axioms.
