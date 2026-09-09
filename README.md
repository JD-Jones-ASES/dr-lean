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

The complete square Dittert theorem for every n>=1, the K=2 theorem and
the all-order large-board theorem, including unique equality, are proved
locally. For K>=4 the latter applies whenever
both dimensions are at least the explicit D_K in the theorem plan; K^21 is
a simpler sufficient threshold. The complete [three-row K=3 family](docs/THREE-ROW-PROOF.md), with arbitrary
N>=3 and its transpose, is also proved locally. The [four-row K=3 strip](docs/ORDER-THREE-RANGES.md)
for N>=960 and the separate [4-by-4 and 4-by-5 K=3 stability certificates](docs/FINITE-K3-CERTIFICATES.md)
are complete too.
The [finite K=3 block bridge](docs/FINITE-K3-BLOCK-SOUNDNESS.md) is complete,
with the complete 4-by-N range 6<=N<=21 and a checked 4-by-959 pilot;
the full 1,330-case replay is in progress.
The complete [four-row K=4 theorem](docs/FOUR-ROW-PROOF.md) is proved locally
for every N>=4 and its transpose, including all boundary matrices and iff equality.
The [finite K=4 probability bridge](docs/FINITE-K4-QUINTIC-BRIDGE.md) now
connects the literal equations to the signed functional, with all 2,704
physical patterns and both fixed seeds checked. The
[fixed-board K=4 theorems](docs/FIXED-BOARD-ORDER-FOUR.md) are complete locally
for 5-by-5 and 20-by-20, with exact uniform equality on the closed simplex. The
[endpoint matrix estimate](docs/ENDPOINT-MATRIX-INTERFACE.md) proves the exact
3/32 margin from explicit moment assumptions. Its
[actual deleted-board kernel](docs/ENDPOINT-ACTUAL-KERNEL-POSITIVITY.md),
[localized load bounds](docs/ENDPOINT-LOCALIZED-KERNEL-BOUNDS.md), and
[one-sided equality closure](docs/ENDPOINT-COLUMN-RIGIDITY.md) are proved.
The [LLL endpoint strip](docs/ENDPOINT-LLL-STRIP-PROOF.md) is complete locally:
m>=128 and 64m^(3/2)<=N<=m(m-1)/20, whenever this interval is nonempty,
including transpose and iff uniform equality.
The remaining promised
rectangular families are in progress.
The completed square proof has readable accounts for [order three](docs/ORDER-THREE-PROOF.md),
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
