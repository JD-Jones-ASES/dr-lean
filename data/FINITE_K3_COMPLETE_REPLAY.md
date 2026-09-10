# Complete finite K=3 envelope replay

All 1,330 canonical case modules and all 87 bounded coverage shards passed
local Lean verification. The source coefficient data remains mathematical
input only; each case independently proves its actual quartic equations,
aggregate kernels and strict positive Gram blocks in Lean.

| Rows | Exact finite columns | Cases |
| --- | --- | --- |
| 4 | 6–959 | 954 |
| 5 | 5–120 | 116 |
| 6 | 6–237 | 232 |
| 7 | 7–24 | 18 |
| 8 | 8–14 | 7 |
| 9 | 9–11 | 3 |

The envelope contains 10,640 strict positive block certificates, 5,320 exact
aggregate-kernel checks, 78,638 positive LDL pivots, and 33 actual quartic
coefficient equations per case. The formula-defined blocks and physical
matrix soundness interfaces are documented in the accompanying certificate
modules. None of these counts is substituted for a proof of the final
matrix inequality: every case exposes `FiniteK3EnvelopeValid`, and the
proved soundness adapter supplies `UniformMaximizer` on the closed simplex.

The original two-case batch replay exited successfully after 665 batches.
The original coverage follower then exited successfully after all 87
shards. Logs had exactly canonical coverage and no failed or warning output.
All generated cases, shards and the shape manifest reproduced byte for byte
under both ordinary Python and `python3 -O`; 19 source/Gram/manifest controls
and seven scheduling controls passed under both interpreters.

The six strip adapters were subsequently compiled in batches of at most two,
followed by the three final production declarations:

- `uniform_maximum_order_three`: every m,n≥3, K=3;
- `uniform_maximum_small_side`: every 2≤K≤min(m,n) with min(m,n)≤4;
- `uniform_maximum_five_by_five`: every 2≤K≤5 on the 5×5 board.

Their combined production build passed 5,708 jobs. The three final test
modules passed separately, including 24 dimension junctions in both
orientations, every closed-simplex equality case, strict boundary-zero
gaps, actual uniform attainment, and the failure of uniqueness at K=1.
Nine final/strip axiom audits expose only `propext`, `Classical.choice`,
and `Quot.sound`. This receipt records local verification; remote CI is a
separate publication gate.

## Reproduction

```sh
python3 scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check
python3 -O scripts/generate_finite_k3_envelope.py --all --dispatch --manifest --check
python3 scripts/test_finite_k3_envelope.py
python3 scripts/test_finite_k3_dispatch.py
python3 scripts/generate_finite_k3_strips.py --check
lake --wfail build Test.OrderThreeFinal Test.SmallSideFinal
lake --wfail build Test.FiveByFiveFinal
```

For an independently bounded full replay, use the existing case and dispatch
scripts with fresh log paths. The completed original logs are retained in
`.verification`; never restart a runner against those paths, since its log
is opened for writing.

Completed case log SHA-256:
`27a195a828a338f3a3a1bc86771601a3db9b7b9e9a6de03460482f4e8d84b624`.
Completed dispatch log SHA-256:
`0a06b7f21e1fc3f2da4d42b1b6fb651fc31eb34630355f46c7aa91bb5bb50f37`.
Canonical generated-file hash manifest SHA-256:
`e8da80eb329df35d220c602b28c2591c968866cd5114c6755c63135180412c5f`.
The local manifest contains 1,417 case/shard source hashes and byte counts.
