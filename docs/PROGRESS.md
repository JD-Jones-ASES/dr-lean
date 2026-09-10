# Current formalization state

Updated 2026-09-09. Fifteen of the twenty required release targets are
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

All results concern actual nonnegative probability matrices, allow zero
entries, and give the sharp uniform bound with equality exactly at uniform.
Rectangular endpoint families include transposition. K=1 retains its
separate nonuniqueness exception. Exact declarations and hypotheses are in
[THEOREMS](THEOREMS.md) and [release-targets.json](../release-targets.json).

## Remaining work

The five pending principal targets are the all-aspect large endpoint,
quadratic, quartic and combined long-column strips, and square near-endpoints
K=n-1 from n=21.

The complete [transition endpoint theorem](ENDPOINT-TRANSITION-PROOF.md)
is a proved component of the all-aspect result. The
[collision-cluster estimate](ENDPOINT-COLLISION-CLUSTER.md) is a proved
input to the long-column work. The [global saturated gauge](ENDPOINT-SATURATED-GAUGE.md)
is now proved for every probability board with m>=96. The
[long-column closure](ENDPOINT-LONG-COLUMN-CLOSURE.md) derives the actual
positive kernels and full uniqueness from explicit contender row and column
caps; deriving those caps remains downstream work.

[Minimum dilation](ENDPOINT-MINIMUM-DILATION.md) and the actual
[zero-rectangle permanent floor](../data/ZERO_RECTANGLE_SOURCE.md) are now
proved and used in the consecutive theorem. The
[near-endpoint padding and discrepancy](../data/NEAR_ENDPOINT_FOUNDATION_SOURCE.md)
and [all-n>=26 scalar tail](../data/NEAR_ENDPOINT_PARAMETERS_SOURCE.md) are
proved. The separate two-independent-zero permanent gap and remaining finite
near-endpoint cuts are active. These foundations do not replace any pending
principal theorem. Original-row and deleted-row avoidance laws remain distinct.

## Verification boundary

The prior fourteen-target mathematical checkpoint
`fd7971f06ecbd2f0dc13c40022f2883ead747d60` passed a combined
`lake --wfail build +DR +Test`: **6,021 jobs**, **195,889 project declarations
audited**, and **2,569 included Lean source hashes unchanged**. No warnings
were emitted. The only permitted transitive axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The isolated source package passed **26** generator/control commands,
including ordinary and optimized Python, and **257** local Markdown links.
The complete K3 [receipt](../data/FINITE_K3_COMPLETE_REPLAY.md) records all
1,330 case proofs, 87 exact dispatch shards, canonical coverage, regeneration
and corruption controls. The tracked import closure contains 2,698 files;
its strict build plan has 1,285 batches of at most two requested modules.
The fifteen-target integration passed `lake --wfail build +DR +Test`:
**6,090 jobs**, **196,549 project declarations audited**, and **2,638 included
Lean source hashes unchanged**, with no warnings. It adds 69 reviewed Lean
modules to the previous closure. Its isolated source package passed **26**
generator/control commands and **281** local Markdown links. The curated
package has **2,781 files**; the strict plan has **1,319** batches of at most
two requested modules. The historical full K3 cold replay was not repeated:
its unchanged sources and all regeneration/corruption controls were checked.

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

The [latest development record](history/2026-09-09-consecutive-endpoint.md)
explains the mathematical additions and verification. Earlier records retain
[initial development](history/2026-09-09-development.md),
[quintic/endpoint work](history/2026-09-09-quintic-endpoint-development.md), and
[the eight-target checkpoint](history/2026-09-09-fixed-board-endpoint-development.md),
and [the fourteen-target checkpoint](history/2026-09-09-complete-low-orders-endpoints.md).
Their historical state is superseded by the current inventory and actual
verification receipts.
