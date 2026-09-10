# Coarse actual row bounds for the transition argument

For an endpoint contender with 2≤m≤n≤10000m², let
b=(n)_m/n^m. Its original row masses satisfy

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

These bounds control reciprocal row masses in the
[collision-avoidance comparison](ENDPOINT-TRANSITION-AVOIDANCE.md).
That relative comparison improves the initial row variance to less than
1/100 in the [bootstrap estimate](ENDPOINT-TRANSITION-BOOTSTRAP.md).

## Formal statements

[TransitionProductBounds](../DR/Endpoint/TransitionProductBounds.lean), [TransitionRowBounds](../DR/Endpoint/TransitionRowBounds.lean).
