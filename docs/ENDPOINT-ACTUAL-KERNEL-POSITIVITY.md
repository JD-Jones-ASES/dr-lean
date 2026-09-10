# The actual endpoint kernel from explicit collision bounds

The endpoint averaging kernel admits a quantitative positive lower bound
from five scalar estimates on the board and its independent-row law. The proof
combines its exact rook normalization with the deletion expectation,
localized collision bounds, and a completion of squares.

`EndpointCollisionKernelBounds P h` records only the five explicit scalar
conditions: row deviation at most 1/9 in squared norm, mean pair ratio at
most 1/4, centered pair squared norm at most 1/64, rowwise deficit-two
ratio at most 1/4, and the coefficient ratio at least 4m². The row deviation
is ∑_i(1−m r_i/h)². The three collision loads are evaluated on
`normalizeRows P`; the coefficient ratio is E/(gamma p0), where
E=e_(m−2)(colSum P) and gamma,p0 are defined below.
Matrix positivity is a conclusion.

For m≥3, nonnegative P with positive row masses, h>0, and positive actual
row avoidance, `averagingKernel_endpoint_gap` proves

```
xᵀ diag(r/h) C diag(r/h) x ≥ (3/32) gamma p0 sum x_i²,
gamma = product(r_i)/h²,   p0=rowAvoidance(normalizeRows P),
C=averagingKernel P (m−2).
```

The following theorem proves that the actual kernel C is positive
definite by inverting the positive row scaling. It permits zero cells
and every signed real vector. The [collision-local strip](ENDPOINT-LLL-STRIP-PROOF.md)
and [transition strip](ENDPOINT-TRANSITION-PROOF.md) derive these five
estimates from their respective dimension hypotheses and the contender
inequality, then use strict column averaging to identify global maxima.

## Formal statements

[RowEndpointKernelPositive](../DR/Endpoint/RowEndpointKernelPositive.lean).
