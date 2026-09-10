# Near-endpoint scalar bounds for n≥26

Define Zₙ=(5/3)(n−1)⁴n³γₙ, where γₙ=n!/nⁿ.
[NearEndpointParameters](../DR/Endpoint/NearEndpointParameters.lean) proves
Z₂₆<3/4 and monotonicity for all n≥26. The recurrence uses
γₙ₊₁≤γₙ/2 and the exact weight estimate
n⁴(n+1)³≤2(n−1)⁴n³.

Consequently the uniform avoidance probability a=(n)ₙ₋₁/nⁿ⁻¹ obeys

```
a < 3 / [5(n−1)⁴ n²],
a < 1/4,
(4/3)n²a < 1.
```

The module also proves the strict scaling comparison with
β=1+1/[4(n−1)²]. These are scalar inequalities. Their application to matrices
uses the independently proved [two-zero permanent bound](../DR/Endpoint/TwoZeroPermanent.lean)
and [transport closure](NEAR_ENDPOINT_CONDITIONAL_SOURCE.md).
Zero deficit remains a separate algebraic boundary case.

```sh
lake --wfail build Test.NearEndpointParameters
```

The tests show Z₂₅>1, so this sufficient estimate does not cover n=25.
Dimensions 21 through 25 use the separate
[finite cut certificates](NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md).
