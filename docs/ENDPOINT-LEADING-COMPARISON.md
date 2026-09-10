# Actual endpoint contender comparison

This package formalizes the retained-uniform comparison from Analytic-Lab
P0174, `ENDPOINT_LEADING_GLOBAL.md` and `ENDPOINT_SATURATED_STABILITY.md`.
It uses the actual iid endpoint functional, including zero rows and columns.
Astra implemented the proof; the root agent independently reviewed the
production modules and persistent controls. Published probability and
symmetric-polynomial theory is cited in the preceding source packages.

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

The source boundary is `m ≤ N`; this is used in the uniform product
estimate. Original and deleted row laws are not interchanged. This
comparison is an input to the long-column closure, not itself a new
endpoint range.

Validation: `lake --wfail build Test.EndpointLeadingComparison` passed 3281
jobs with nine persistent examples and no warnings. The three exported axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Controls include closed product endpoints, the empty product, failure
without the coordinate upper cap, the exact nonzero three-draw remainder,
a genuine uniform contender, and a balanced diagonal board that violates
the comparison when the contender premise is omitted. No `sorry`, new
axiom, or native evaluation is used.
