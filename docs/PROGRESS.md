# Current formalization state

Updated 2026-09-09. All twenty required release targets are
proved locally. This dated record captures local completion before
independent release verification. The exact-commit
[CI workflow](https://github.com/JD-Jones-ASES/dr-lean/actions/workflows/development.yml)
records that separate outcome. Full arbitrary-rectangle Rybin P2 remains open.

## Completed principal results

- All square Dittert orders, with sharp value and unique equality.
- K=2 and [K=3](ORDER-THREE-COMPLETE.md) on every admissible rectangle.
- K=4 on every [four-row rectangle](FOUR-ROW-PROOF.md), and on
  [5-by-5 and 20-by-20](FIXED-BOARD-ORDER-FOUR.md).
- The all-order large-board threshold and its simpler K^21 corollary.
- Every admissible K when the smaller side is at most four, and every
  K=2,3,4,5 on 5-by-5.
- The [arithmetic endpoint range](ENDPOINT-BOUNDARY-SCALING.md):
  m>=128 and m<=N<=m(m-1)/(22 log m).
- The [consecutive endpoint range](ENDPOINT_CONSECUTIVE_CUTS.md):
  m>=19 and N=m+1, with transpose.
- The [short and doubled endpoint ranges](ENDPOINT_NEAR_DOUBLE.md):
  m>=117, m<=N<=2m; and m>=80, N=2m.
- The [LLL endpoint strip](ENDPOINT-LLL-STRIP-PROOF.md):
  m>=128 and 64m^(3/2)<=N<=m(m-1)/20, whenever nonempty.

- Every endpoint aspect ratio [N>=m for m>=10^18](ENDPOINT-ALL-ASPECTS.md).
- The [quadratic](ENDPOINT-QUADRATIC.md), [quartic](ENDPOINT-QUARTIC.md), and
  [combined](ENDPOINT-COMBINED.md) endpoint strips: respectively
  m>=96,N>=10000m^2; m>=16,N>=20000m^4; m>=5,N>=10^11m^2.
- The [square near-endpoint](SQUARE_NEAR_ENDPOINT.md): n>=21 and K=n-1.

Every rectangular result concerns nonnegative matrices of mass one; the
Dittert statement uses mass n. All allow zero entries and give the sharp
uniform bound with equality exactly at the corresponding uniform matrix.
Rectangular endpoint families include transposition. K=1 retains its
separate nonuniqueness exception. Exact declarations and hypotheses are in
[THEOREMS](THEOREMS.md) and [release-targets.json](../release-targets.json).

## Completed final proof and remaining release work

The square near-endpoint theorem has only its dimension hypothesis. The
[actual two-zero matrix reduction](TWO_ZERO_REDUCTION.md),
[exact matrix permanent floors](TWO_ZERO_PERMANENT.md), finite dimensions
21 through 25, and infinite range from 26 now form a complete proof.
Additional zeros, zero deficit, unit dilation, and exact uniform equality
remain covered. The principal and its boundary tests passed a clean
3,565-job replay, with only the three standard logical axioms.

The remaining work is repository-wide release verification: all twenty
public statements and matching proofs, metadata, independent Linux CI,
Comparator and NanoDa, and exact default-branch verification. Full P2
outside the stated ranges remains open.

## Verification boundary

The complete twenty-target integration passed
`lake --wfail build +DR +Test +Solution`: **6,196 jobs**, **197,437 project
and wrapper declarations audited**, and **2,736 included Lean source hashes
unchanged**, with no warnings. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted transitive axioms. The public wrappers separately
passed a complete 47-declaration audit and exact statement/semantic controls.

The complete K3 [receipt](../data/FINITE_K3_COMPLETE_REPLAY.md) retains all
1,330 case proofs and 87 exact dispatch shards. Its historical local cold
replay was not repeated; the independent Linux job starts from pinned
mathematical dependencies and checks the complete tracked proof closure.
The isolated **2,913-file** source package passed
**30** generator/source/control commands, including
normal and optimized Python, and **344** local Markdown links.
Strict tracked coverage has **1,368** batches of at most two requested modules.
All included production modules are reachable by the global axiom audit.
The verifier driver's 35 static/mock controls pass normally and optimized;
they establish orchestration behavior, not a Linux kernel pass.

Independent CI is required for the exact private checkpoint and its default
branch before release. At local integration, private main and the durable
source checkout were at independently verified `71ab5fb1e4bae27fbd43f26ab06f2e1646750836`.
Its [main replay](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34387704231)
succeeded. It is historical evidence for that earlier commit only.
Earlier exit-143 runs remain unaccepted; their termination cause is
unconfirmed. A local proof or a dry build plan does not replace CI.

The [public-release gate](VERIFICATION.md) requires both complete proof
build and independent kernels on the exact commit. This record establishes
local completion. At this checkpoint, complete twenty-target CI, Comparator
and NanoDa remain pending; the current exact-commit workflow and its artifacts
record that separate outcome, not the historical run cited above. JD submits to Palomar manually after the gate passes.

## Detailed records

The [latest development record](history/2026-09-09-complete-twenty-targets.md)
explains the mathematical additions and verification. Earlier records retain
[initial development](history/2026-09-09-development.md),
[quintic/endpoint work](history/2026-09-09-quintic-endpoint-development.md), and
[the eight-target checkpoint](history/2026-09-09-fixed-board-endpoint-development.md),
and [the fourteen-target checkpoint](history/2026-09-09-complete-low-orders-endpoints.md),
and [the fifteen-target checkpoint](history/2026-09-09-consecutive-endpoint.md),
and [the nineteen-target checkpoint](history/2026-09-09-long-column-endpoints.md).
Their historical state is superseded by the current inventory and actual
verification receipts.
