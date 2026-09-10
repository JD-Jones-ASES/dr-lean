# dr-lean — Dittert and rectangular semimatching inequalities

A Lean 4 formalization of the square Dittert inequality and the rectangular
semimatching results developed in Analytic-Lab. **Private development;
the complete release theorem set is not yet formalized.** A successful development
build checks completed modules only. It is not a release-readiness claim.

For a nonnegative M-by-N matrix of total mass one, draw K cells independently
with replacement. P2 asks whether the probability of distinct rows **or**
distinct columns is uniquely maximized by the uniform matrix. The OR is
inclusive. Dittert is exactly the square endpoint M=N=K. Boundary matrices
and arbitrary marginals are included; K=1 is separated from uniqueness.

The full release scope is fixed in [the theorem plan](docs/THEOREMS.md):
complete square Dittert by our alternative proof, complete rectangular K=3,
complete four-row K=4, the all-order large-board theorem, the large-endpoint
ranges, and their stated corollaries. Full arbitrary-rectangle P2 remains open.

Fifteen of the twenty required release targets are now proved locally:
all square Dittert orders, K=2 and K=3 on all admissible rectangles,
K=4 on every four-row rectangle and on 5-by-5 and 20-by-20,
the two large-board thresholds, all admissible orders for smaller side at
most four and for 5-by-5, the arithmetic, consecutive, near-square and doubled endpoint
ranges, and the LLL endpoint strip. The remaining endpoint families are active work.

The [complete K=3 proof](docs/ORDER-THREE-COMPLETE.md) joins all 1,330
kernel-verified finite certificates and 87 coverage shards with the proved
infinite ranges. The [four-row K=4 proof](docs/FOUR-ROW-PROOF.md) and
[fixed-board K=4 proofs](docs/FIXED-BOARD-ORDER-FOUR.md) likewise retain
actual polynomial identities, physical matrix soundness and strict equality.

The [arithmetic endpoint proof](docs/ENDPOINT-BOUNDARY-SCALING.md) applies
for m>=128 and m<=N<=m(m-1)/(22 log m). Its common-divisor criterion connects
actual marginal deficits, balanced transport, rectangular padding and the
internally proved boundary permanent bound. The
[LLL endpoint strip](docs/ENDPOINT-LLL-STRIP-PROOF.md) applies for m>=128 and
64m^(3/2)<=N<=m(m-1)/20 when nonempty. A separate
[transition theorem](docs/ENDPOINT-TRANSITION-PROOF.md) now covers
m>=10^18, m<=N, m(m-1)<=20N and N<=10000m^2. This transition result is one component
of the still-pending all-aspect endpoint theorem, not an additional completed
release target. All these results include transpose and iff uniform equality. The
[near-square and doubled ranges](docs/ENDPOINT_NEAR_DOUBLE.md) now cover
m>=117 with m<=N<=2m, and m>=80 with N=2m, respectively.
The [consecutive endpoint proof](docs/ENDPOINT_CONSECUTIVE_CUTS.md) covers
every m>=19 on m by (m+1), and transpose. Exact finite cut inequalities for
19<=m<=29 join an all-integer factorial recurrence from m=30.

The square proof has readable accounts for [order three](docs/ORDER-THREE-PROOF.md),
[order four](docs/ORDER-FOUR-PROOF.md), [order five](docs/ORDER-FIVE-PROOF.md),
and [all orders at least six](docs/SPECTRAL-PROOF.md).

## Read and build

- [Sources and attribution](docs/SOURCES.md): Rybin's supplied post,
  Cheon–Wanless, the earlier public complete Dittert proof, and Lab evidence.
- [Theorems and dependency order](docs/THEOREMS.md): every required target and
  its current status; no replacement of a global result by finite tests.
- [Rectangular foundations](docs/RECTANGULAR-FOUNDATIONS.md): support exclusions,
  the actual four-sample averaging kernel and endpoint concentration prerequisites.
- [Four-row inputs](docs/FOUR-ROW-INPUTS.md): actual collision remainders,
  the complete corrected minorant, analytic K=4 tail, and finite-certificate matrix reduction.
- [Finite K=4 roles](docs/FINITE-K4-ROLES.md): complete physical role coverage,
  quintic symmetrization and the remaining positivity obligations.
- [Square prerequisites](docs/SQUARE-DEPENDENCIES.md): verified Mathlib
  inventory and the completed transport and permanent prerequisites.
- [Verification and publication](docs/VERIFICATION.md): development checks,
  complete proof checks, independent replay, and the exact public-release gate.

```sh
lake exe cache get
lake build DR Test
python3 scripts/check-source.py
```

`DR/Definitions.lean` and `DR/Semimatching.lean` fix the ordinary matrix and
probability meanings. `DR/Probability.lean` proves the finite iid sampling
identities. `DR/Collision/` supplies the rectangular probability arguments;
`DR/Square/` supplies the permanent and stationary-cut arguments. Proofs use
Lean's kernel, without custom axioms or native computation trust extensions.

The public release will include readable Challenge/Solution modules,
source metadata, a complete transitive axiom audit, and Comparator/NanoDa
verification. The repository stays private until the advertised theorem set
passes those checks and independent CI on its exact default-branch commit.
JD will submit to Palomar manually.

Human responsibility: JD Jones. Mathematical and formal development uses
OpenAI Codex/Astra and parallel agents; see [disclosure](DISCLOSURE.md).
