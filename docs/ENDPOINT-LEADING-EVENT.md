# Exact endpoint collision correction

`LeadingEvent.endpoint_failure_leading_lower` proves, for every nonnegative
probability board with at least three rows,

```
1 − F_m(P) ≥ 1 − m! e_m(c)
            − choose(m,2) sum_j (c_j^2 − alpha_j^2),
alpha_j = endpointLeadingColumnCost P j.
```

This is the actual iid failure probability. The proof uses an equivalent
independent-row form of the event union argument in P0174
`ENDPOINT_POLYNOMIAL_STRIPS.md`. The exact endpoint rook identity says the
row-distinct contribution with a column collision is
`m!*(product(r)−rowAvoidance(P))`. When all rows are positive, normalization
gives the original independent-row law, its true pair-collision union
bound, and the polynomial kernel identity
`sum(c^2−alpha^2)=2*gamma*rowCollisionIntensity(normalizeRows P)`.
The factor `choose(m,2)*2*(m−2)!=m!` is proved exactly.

A zero row is handled directly: its row product is zero and every actual
column quadratic equals the square of the column mass. No zero row is
normalized into a probability law. Individual zero columns are allowed.
No contender, stationarity, or global gauge conclusion is a premise.

`lake --wfail build Test.EndpointLeadingEvent` passed 3,239 jobs, seven
examples and five standard-only axiom audits. Controls include the omitted
factor two, the lowest factorial identity, an actual single-column collision
law, the zero-row cost identity, and the full failure bound at that boundary.
