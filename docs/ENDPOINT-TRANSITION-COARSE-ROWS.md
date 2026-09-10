# Coarse actual row bounds for the transition argument

`TransitionProductBounds.lean` and `TransitionRowBounds.lean` formalize
Section 1 of the accepted Lab `ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`.
For an actual endpoint contender on `2<=m<=n<=10000*m^2`, they derive

```
q=1-b >= 1/40001 > 1/50000,
1/150000 < m*rowSum_i < 32,
sum (m*rowSum_i-1)^2 < 1024,
endpointRowReciprocalDeviation P < 160000000.
```

The literal uniform avoidance product gives the first bound. The actual
contender product is at least `q`. A finite-product coordinate envelope
forces both coordinate caps; its monotonic bound is derived from the
exponential tangent inequality, without assuming differentiability of an
optimizer. The logarithm estimate on `(0,32]` follows exactly from the
square-root identity and `log(sqrt y)<=sqrt y-1`. Summing uses the exact
product logarithm and finite coordinate sum. The reciprocal deviation
then retains the individual positive row denominators.

The generic scalar results permit zero input coordinates and empty hosts;
positivity is derived where the product lower bound demands it. Actual
matrix results require only nonnegativity, total mass one, the endpoint
contender relation and the stated dimensions. No stationary condition,
row-shape hypothesis, endpoint gauge or deleted-board replacement is used.

Verification: `lake build Test.TransitionRowBounds` passed 3166 jobs,
with ten standard-only axiom audits and no warnings. Tests cover a nonconstant
rational vector, the exact reciprocal deviation, the closed upper logarithm
cap, empty hosts, zero-product and logarithm-domain failures, and failure
of the uniform probability bound if the column-range cap is omitted.

These are initial estimates, not a transition maximizer theorem. The
refined collision-intensity/LLL comparison and subsequent small row-deficit
bootstrap remain separate obligations before this advances an endpoint range.
