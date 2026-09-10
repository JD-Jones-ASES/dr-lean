# Size-sensitive endpoint marginal bounds

Let P be a nonnegative m by n matrix of total mass one, with 2≤m≤n,
and suppose its m-draw separation probability is at least the uniform value.
Write r and c for its row and column masses, a=m!/m^m, b=(n)_m/n^m,
R=m^m∏r_i, S=m! e_m(c)/b, and T=m^m rookSum(P,m).
Here e_m sums products over m-element column subsets, and rookSum sums
products over matchings without ordering their rows. The estimates below
hold for any real H satisfying

```
H ≥ 1,    m b/[2(1-b)] ≤ (H-1)^2,
```

The scalar cap implies m r_i≤H for every row. The choice H=101/100
satisfies it throughout the finite consecutive range 19≤m≤29, n=m+1;
the general marginal inequalities do not require that particular choice.

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

The row cap comes from the proved product-deficit singleton
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

For a cut with positive demand p=k/m+l/n−1, divide the joint estimate
by p². The resulting coefficient is [A_k+(a/b)B_l]/p². The
[consecutive endpoint proof](ENDPOINT_CONSECUTIVE_CUTS.md) uses this
coefficient to control the loss in a balanced dilation and compare its
complementary zero rectangle with a permanent lower bound.

## Formal statements

[ConsecutiveCutGeometry](../DR/Endpoint/ConsecutiveCutGeometry.lean), [ConsecutiveCutMarginals](../DR/Endpoint/ConsecutiveCutMarginals.lean), [ConsecutiveCutShared](../DR/Endpoint/ConsecutiveCutShared.lean).
