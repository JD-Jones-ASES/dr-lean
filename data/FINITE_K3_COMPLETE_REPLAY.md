# Complete finite K=3 coefficient envelope

The exact coefficient envelope contains 1,330 canonical rectangles:

| Rows | Columns | Cases |
| --- | --- | --- |
| 4 | 6–959 | 954 |
| 5 | 5–120 | 116 |
| 6 | 6–237 | 232 |
| 7 | 7–24 | 18 |
| 8 | 8–14 | 7 |
| 9 | 9–11 | 3 |

Each case proves 33 quartic coefficient equations, four aggregate-kernel
identities, and eight strictly positive Gram-block certificates. Altogether
there are 10,640 strict blocks, 5,320 kernel checks and 78,638 positive LDL
pivots. The [rational coefficients](FINITE_K3_SOURCE.md) define the physical
matrices; the counts themselves are not premises of a matrix inequality.

Every case constructs `FiniteK3EnvelopeValid`. The
[soundness theorem](../DR/Certificates/FiniteK3EnvelopeSoundness.lean) transfers
these exact equations and kernels to the uniform-maximizer inequality on the
full closed probability simplex, including its unique equality case.

The finite strips combine with analytic dimension bounds in
[the all-rectangle K=3 theorem](../DR/Rectangular/OrderThreeFinal.lean).
The [small-side theorem](../DR/Rectangular/SmallSideFinal.lean) covers
2≤K≤min(m,n) when min(m,n)≤4. The
[5×5 theorem](../DR/Rectangular/FiveByFiveFinal.lean) covers 2≤K≤5.
The case K=1 is excluded because every probability matrix has success one.

```sh
python3 scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check
python3 -O scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check
python3 scripts/test_finite_k3_envelope.py
python3 scripts/test_finite_k3_dispatch.py
python3 scripts/generate_finite_k3_strips.py --check
lake --wfail build Test.OrderThreeFinal Test.SmallSideFinal
lake --wfail build Test.FiveByFiveFinal
```

The case and dispatch checks verify the entire stated envelope. Matrix tests
include dimension junctions in both orientations, zero entries, uniform
attainment, and the failure of uniqueness at K=1.
