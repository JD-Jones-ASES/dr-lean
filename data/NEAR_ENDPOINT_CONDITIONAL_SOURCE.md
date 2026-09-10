# Near-endpoint closure from a two-zero permanent bound

For every n≥21, [NearEndpointConditional](../DR/Endpoint/NearEndpointConditional.lean)
turns a specified permanent bound for doubly stochastic (n+1)×(n+1) matrices
with two independent zeros into the n×n, K=n−1 uniform-maximizer theorem.
This interface separates the transport argument from its permanent estimate.
The estimate is proved in [TwoZeroPermanent](../DR/Endpoint/TwoZeroPermanent.lean)
and discharged in [SquareNearEndpoint](../DR/Endpoint/SquareNearEndpoint.lean),
which gives the unconditional result.

For n=21,…,25, the proof uses the minimum dilation q, an active positive cut,
and its complementary zero rectangle. The case q=1 is handled separately;
otherwise a whole cut would contradict q<1. The
[finite cut certificates](NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md) provide the
strict quadratic scaling gap. For n≥26, shared-deficit balanced domination
and [the scalar tail](NEAR_ENDPOINT_PARAMETERS_SOURCE.md) exclude boundary
maximizers. The normalization is the one-zero boundary permanent floor μₙ₊₁,
rather than the uniform permanent γₙ₊₁.

The positivity-to-uniformity step applies to the full closed probability
simplex and preserves the unique equality case. The intermediate hypothesis
`TwoIndependentZeroPermanentBound` quantifies actual matrices, including
additional zeros; it is not an assumed optimizer shape.

```sh
lake --wfail build Test.NearEndpointConditional Test.SquareNearEndpoint
```

The tests cover the finite/analytic junction, zero exceptional parameters,
zero inheritance at scaling one, and the necessity of positive scaling.
