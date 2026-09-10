# Active cuts for the square near-endpoint problem

[NearEndpointCuts](../DR/Endpoint/NearEndpointCuts.lean) applies to actual
n×n probability matrices with n≥3. Let a=(n)ₙ₋₁/nⁿ⁻¹ and let δ be the
shared rook-deficit budget. The normalized elementary deficits bound marginal
variance by 2d/[n(1−a)]. Projection onto centered subset indicators gives the
factor k(n−k). For a positive cut demand p=(k+l−n)/n, the squared discrepancy
is at most p² Cₖₗ δ/(1−a), where

```
Cₖₗ = 2[k(n−k)+l(n−l)] / (k+l−n)².
```

The bounds retain whole and empty subsets. Under a≤1/4 and (4/3)n²a<1,
balanced domination makes every positive cut mass positive. Minimum dilation
then gives 0<q≤1, balanced B, qB≤P and a positive active cut with a
complementary zero rectangle. Active equality yields
(1−q)²≤Cₖₗδ/(1−a), including δ=0. The guards hold for all n≥21 by the
five [finite cases](NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md) and the
[tail](NEAR_ENDPOINT_PARAMETERS_SOURCE.md).

The complementary axes embed into the corner-zero padded matrix D(B).
The [zero-rectangle bound](ZERO_RECTANGLE_SOURCE.md) gives

```
per(D(B)) ≥ γₖ₊₁ γₗ₊₁ / γₖ₊ₗ₊₁₋ₙ.
```

On appropriate cuts this is combined with the independently proved
[two-zero bound](../DR/Endpoint/TwoZeroPermanent.lean). Both floors concern
the actual padded matrix. Their use in the complete inequality is in
[SquareNearEndpoint](../DR/Endpoint/SquareNearEndpoint.lean).

```sh
lake --wfail build Test.NearEndpointCuts
```

Tests include mixed and axis cuts, whole and zero-demand boundaries, the
residual-order denominator, dimensions 21 and 25, and δ=0 forcing q=1.
