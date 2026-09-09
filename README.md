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

The complete K=2 theorem and the all-order large-board theorem, including
unique equality, are now proved locally. For K>=4 the latter applies whenever
both dimensions are at least the explicit D_K in the theorem plan; K^21 is
a simpler sufficient threshold. The square Dittert proof and the other
promised rectangular families remain in progress.

## Read and build

- [Sources and attribution](docs/SOURCES.md): Rybin's supplied post,
  Cheon–Wanless, the earlier public complete Dittert proof, and Lab evidence.
- [Theorems and dependency order](docs/THEOREMS.md): every required target and
  its current status; no replacement of a global result by finite tests.
- [Square prerequisites](docs/SQUARE-DEPENDENCIES.md): verified Mathlib
  inventory, completed transport proof and remaining permanent prerequisites.
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
