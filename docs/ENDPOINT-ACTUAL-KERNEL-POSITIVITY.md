# The actual endpoint kernel from explicit collision bounds

`DR/Endpoint/RowEndpointKernelPositive.lean` completes the conditional
localized matrix theorem of P0174 `ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`.
It uses the existing `averagingKernel`, its proved rook normalization,
the actual independent-row expectation, the localized collision estimates,
and the exact scalar square completion.

`EndpointCollisionKernelBounds P h` records only the five explicit scalar
conditions: row deviation at most 1/9 in squared norm, mean pair ratio at
most 1/4, centered pair squared norm at most 1/64, rowwise deficit-two
ratio at most 1/4, and the coefficient ratio at least 4m². These quantities
are evaluated on `normalizeRows P`. Matrix positivity is a conclusion.

For nonnegative P with positive row masses, h>0, and positive actual
row avoidance, `averagingKernel_endpoint_gap` proves

```
q(C, diag(r/h) x) ≥ (3/32) gamma p0 sum x_i²,
gamma = product(r_i)/h².
```

The following theorem proves that the actual kernel C is positive
definite by inverting the positive row scaling. It permits zero cells
and every signed test vector. The source's dimension-range estimates
remain separate: this conditional theorem does not itself assert any
new rectangle range or global P2 result.

Replay: `lake build Test.RowEndpointKernelPositive`. The persistent
example is the 4×4 diagonal probability matrix, with twelve zero cells,
whose actual row law is deterministic and collision-free. Its explicit
coefficient ratio is 96. The tests prove actual kernel positivity and
the quantitative bound for a mixed-sign vector, while rejecting a
silently normalized zero row.
