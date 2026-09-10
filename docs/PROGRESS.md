# Current formalization state

Updated 2026-09-09. Nineteen of the twenty required release targets are
proved locally. The repository remains private, and the complete release
gate has not passed. Full arbitrary-rectangle Rybin P2 remains open.

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

All results concern actual nonnegative probability matrices, allow zero
entries, and give the sharp uniform bound with equality exactly at uniform.
Rectangular endpoint families include transposition. K=1 retains its
separate nonuniqueness exception. Exact declarations and hypotheses are in
[THEOREMS](THEOREMS.md) and [release-targets.json](../release-targets.json).

## Remaining work

The sole pending principal target is the square near-endpoint K=n-1 for
n>=21. Its actual corner-zero padding, shared marginal discrepancy, balanced
dilation, [finite cut certificates](../data/NEAR_ENDPOINT_FINITE_CUTS_SOURCE.md)
and infinite scalar tail are proved. The [two-parameter scalar permanent
bound](../data/TWO_ZERO_POLYNOMIAL_SOURCE.md), including its
[logarithmic tail](../data/TWO_ZERO_LOG_TAIL_SOURCE.md), is also proved.

The [actual face stationarity](PERMANENT_FACE_STATIONARITY.md) and
[strict support structure](TWO_ZERO_FACE_SUPPORT.md) apply to minima on the
full two-zero doubly stochastic face, permitting additional zeros.
Repeated-support averaging, matrix reduction to the scalar formula, and
final near-endpoint assembly remain active. The scalar formula alone is
not an arbitrary-matrix permanent theorem.

The long-column principal proofs now derive the actual row and column caps
from the [leading comparison](ENDPOINT-LEADING-COMPARISON.md),
[coarse gauge](ENDPOINT-COARSE-GAUGE.md), and
[saturated gauge](ENDPOINT-SATURATED-GAUGE.md). Original-row and deleted-row
avoidance laws remain distinct through the retained-kernel argument.

## Verification boundary

The nineteen-target integration passed `lake --wfail build +DR +Test`:
**6,168 jobs**, **197,200 project declarations audited**, and **2,708 included
Lean source hashes unchanged**, with no warnings. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted transitive axioms.
It adds 70 independently reviewed Lean modules to the fifteen-target closure.

The isolated **2,869-file** source package passed **26** generator/control
commands, including ordinary and optimized Python, and **319** local Markdown
links. Strict import coverage contains **1,354** batches of at most two
requested modules, with every included production module reachable by the
global axiom audit. Frozen source bytes and explicit whitespace were checked.
The complete K3 [receipt](../data/FINITE_K3_COMPLETE_REPLAY.md) retains all
1,330 case proofs and 87 exact dispatch shards. Its historical cold replay
was not repeated; unchanged sources and all regeneration/corruption controls
were checked again.

Independent CI is required for the exact private checkpoint and its default
branch before release. Private main and the durable source checkout remain
at independently verified `71ab5fb1e4bae27fbd43f26ab06f2e1646750836`.
Its [main replay](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34387704231)
succeeded. Later local proofs have not yet cleared that independent gate.
Earlier exit-143 runs remain unaccepted; their termination cause is
unconfirmed. A local proof or a dry build plan does not replace CI.

The complete [public-release gate](VERIFICATION.md), including all twenty
targets, Challenge/Solution, Comparator and NanoDa, remains pending. JD
will submit to Palomar manually after that gate passes.

## Detailed records

The [latest development record](history/2026-09-09-long-column-endpoints.md)
explains the mathematical additions and verification. Earlier records retain
[initial development](history/2026-09-09-development.md),
[quintic/endpoint work](history/2026-09-09-quintic-endpoint-development.md), and
[the eight-target checkpoint](history/2026-09-09-fixed-board-endpoint-development.md),
and [the fourteen-target checkpoint](history/2026-09-09-complete-low-orders-endpoints.md),
and [the fifteen-target checkpoint](history/2026-09-09-consecutive-endpoint.md).
Their historical state is superseded by the current inventory and actual
verification receipts.
