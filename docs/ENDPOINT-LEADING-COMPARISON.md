# Actual endpoint contender comparison

The endpoint failure probability controls the dispersion of the leading
column costs. The comparison below includes every nonnegative probability
board whose value is at least the uniform value, with zero rows or columns
permitted in the initial domain.

For an `m × N` probability board, put `a = m! / m^m`,
`A = choose(m,2)`, `b = (m−2)(m+1)/2`, `c_j = colSum P j`,
`alpha_j = endpointLeadingColumnCost P j`, and `G = sum alpha_j`.
For every actual uniform contender with `3 ≤ m ≤ N` and a common cap
`c_j ≤ C`, the theorem `endpoint_contender_leading_comparison` proves

```
G² − (1−a) + N sum_j (alpha_j − G/N)²
  ≤ N b C sum_j (c_j − 1/N)² + a b/(2N).
```

The proof combines the genuine original-row collision union bound in
[LeadingEvent](ENDPOINT-LEADING-EVENT.md), the exact two-column comparison in
[ColumnFailureComparison](ENDPOINT-COLUMN-COMPARISON.md), and the uniform
falling-factorial remainder proved in `UniformCollisionRemainder.lean`:

```
0 ≤ A/N − (1−(N)_m/N^m) ≤ A b/(2N²).
```

That remainder comes from a finite product Bonferroni inequality on the
closed cube. The diagonal square contribution is retained; the needed
upper bound uses `j² ≥ j`, so no asymptotic approximation is involved.
The final comparison retains the uniform correction before cancellation
by the positive quantity `A/N`. It assumes neither a small cap nor a
positive leading kernel, row concentration, or stationarity.

The dimension condition `m ≤ N` is used in the uniform product estimate.
The comparison uses the original row law and supplies the cost-variance
bound in the [long-column concentration argument](ENDPOINT-LONG-COLUMN-CONCENTRATION.md).

## Formal statements

[LeadingEvent](../DR/Endpoint/LeadingEvent.lean), [ColumnFailureComparison](../DR/Endpoint/ColumnFailureComparison.lean), [UniformCollisionRemainder](../DR/Endpoint/UniformCollisionRemainder.lean).
