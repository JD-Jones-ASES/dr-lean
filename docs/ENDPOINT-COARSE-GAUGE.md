# Quantitative endpoint leading gauge for every m >= 5

For a row-mass vector r, let B(r) have diagonal entries one and
off-diagonal entries 1−(m−2)!∏_{a∉{i,j}}r_a. For each column v_j of P,
define its cost as √(v_jᵀB(r)v_j), and let G be the sum of these costs.
The following inequalities give a positive modulus in the row variance.

For every nonnegative `m × N` probability board with `m >= 5`, let
`a = m!/m^m`, `s0 = sqrt(1-a)`, `V = sum_i (r_i-1/m)^2`, and
`G = sum_j sqrt(v_j^T B(r) v_j)`. The final theorems prove

```
endpointLeadingGauge_coarse_lower:    s0 + (a/1000)V <= G
endpointLeadingGauge_coarse_sq_gap:   (a/1000)V <= G²-(1-a)
endpointLeadingGauge_coarse_sq_lower: 1-a <= G²
endpointLeading_quadratic_coarse_lower:
  (1-a+(a/1000)V)/N <= sum_j v_j^T B(r) v_j.
```

The last statement explicitly assumes `N > 0`. The others derive that
condition from the probability mass. These results include zero cells,
zero rows, zero columns, and `N < m`. They are leading-gauge inequalities;
the final rectangular P2 ranges require the separate actual contender
comparison and collision-kernel closure. See
[the actual comparison](ENDPOINT-LEADING-COMPARISON.md) and
[the saturated refinement](ENDPOINT-SATURATED-GAUGE.md).

The proof is split into five modules:

- `LeadingCoarseScalars` proves the exact negative-discriminant certificate
  for every real `k >= 3` and every real `d`. Shifting `k = t+3` leaves
  the positive cubic with coefficients `165275, 1892649, 6593169, 6306691`.
  A proved linear numerator comparison gives the entire `0 < T <= 11`
  interval bound. No finite parameter sample is used.
- `LeadingCoarseStationary` derives that interval from the actual scalar
  stationarity equation, the common gradient cap, and weighted Cauchy.
  With `H=1-G-2a/1000`, it proves `H >= 497a/1000`, `D/H > 1`, and
  `(C-G+2a/1000)/H < 11`. Summing the products of distances to the two
  endpoints yields the strict row-square bound and the original kernel's
  positive definiteness.
- `LeadingCoarseProduct` proves the closed-simplex product estimate
  `product_i(m r_i) <= 1-V` from the proved degree-two
  Newton-Maclaurin comparison. The actual positive-semidefinite norm
  bound then gives `G-s0 >= aV/2`; the PSD premise remains explicit in
  this intermediate lemma.
- `LeadingCoarseMinimum` constructs a genuine minimum of `G-(a/1000)V`
  on the full compact probability simplex. The uniform comparator and
  zero-row identity force positive rows. The true feasible row-scaling
  derivative supplies the preceding stationary data, so the original
  kernel is proved positive definite at the minimum. Its value is at
  least `s0`.
- `LeadingCoarse` transfers that minimum bound to every probability board,
  then proves the squared and column-quadratic bounds. No positivity,
  stationarity, row cap, or optimizer shape is assumed in these global
  statements.

## Formal statements

[LeadingCoarseScalars](../DR/Endpoint/LeadingCoarseScalars.lean), [LeadingCoarseStationary](../DR/Endpoint/LeadingCoarseStationary.lean), [LeadingCoarseProduct](../DR/Endpoint/LeadingCoarseProduct.lean), [LeadingCoarseMinimum](../DR/Endpoint/LeadingCoarseMinimum.lean), [LeadingCoarse](../DR/Endpoint/LeadingCoarse.lean).
