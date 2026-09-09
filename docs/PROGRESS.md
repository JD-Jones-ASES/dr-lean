# Current formalization state

Updated 2026-09-09. The complete release goal remains active.

Completed locally:

- Exact real matrix domain, marginals and closed probability simplex.
- Ordered iid sample mass, normalization, nonnegativity, inclusive-OR
  inclusion-exclusion, complements, monotonicity and probability bounds.
- Exact marginalization under any injective selection of iid sample indices,
  including empty and full selections and arbitrary weighted observables.
- Uniform semimatching value for every sample order, including zero,
  one and orders exceeding board dimensions; explicit injection counts.
- Finite weighted Bonferroni and the exact scalar concentration bootstrap.
- Permanent monotonicity, constant evaluation, row/column scaling,
  triangular-block factorization and diagonal-block lower bounds.
- The full finite real-capacity transport cut criterion and dominated doubly
  stochastic matrix construction, including zero demand and empty matrices.
- Exact square endpoint identity and scaling, for arbitrary real matrices.
- Equivalence of square P2 and Dittert, including equality, and complete
  Dittert orders one and two.
- Sample-index collision witnesses: exact count, exact failure union,
  Bonferroni connection and uniform event mass, including overlapping pairs.
- The complete K=2 uniform maximum and unique equality theorem, through
  the exact squared-distance deficit identity.
- The complete first collision-moment identity for every sample order at
  least four: coincident, overlapping and disjoint witness classes are
  counted exactly and every event mass comes from actual iid sampling.
- Entropy on the closed simplex and the mixed/disjoint collision-moment
  lower bounds; these give the uniform first-moment bound plus its exact
  cell-variance term.
- Continuity, compactness and global-maximizer existence for the actual
  objective, with transpose, matrix-axis and sample-index symmetries.
- The distinct-witness intersection bound from proved combinatorial
  deletion and exact integration of the removed sample coordinate.
- Actual-matrix contender concentration: the normalized cell variance and
  largest marginal satisfy the two stated strict collision bounds.
- All-order threshold arithmetic: the explicit dimension bound is at most
  K^21, and every contender at that threshold meets the stated variance
  and marginal smallness bounds.
- The sharp univariate capacity step for nonnegative affine products,
  including zero constants and slopes; exact doubly stochastic product
  capacity one and the finite telescoping product of capacity losses.

In progress:

- Conditional occupation quadratic inequalities and the exact blending identity.
- Van der Waerden's permanent lower bound and equality prerequisites.

The principal square, K=3, K=4, all-order and large-endpoint results remain
unformalized. Van der Waerden with equality is not present in the pinned
Mathlib and still requires a proof. The real-capacity transport prerequisite
has been proved in this project.
Read docs/THEOREMS.md for the full target inventory. Do not publish based on
the completed foundations alone.

Initial private remote checkpoint: `007871efa78c9372be39f7b0b51e1286d758d75f`.
Its local build passed and audited 282 project declarations. Seven source
guard controls and six Lean semantic checks passed. Its
[independent development CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34356306914)
also passed. This checks completed modules and does not complete the release.

The subsequent local combined build including the first moment, entropy and
compactness modules passed and audited 410 project declarations. Its exact
commit `06b67b054494431c8b86a3e450c820956a63d531` also passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34357179545)
and was advanced to private main. The new capacity route and its outstanding
stability obligations are documented in [CAPACITY-ROUTE](CAPACITY-ROUTE.md).

The next combined local build includes witness intersections, actual-matrix
concentration, threshold arithmetic and both capacity modules: 3,221
dependency jobs passed and the audit covered 526 project declarations.
The new boundary checks retain the zero-capacity equality example and
distinguish positive demand from zero demand on zero-capacity boards.

Working checkout during initial development: /private/tmp/dr-lean. The private
remote is https://github.com/JD-Jones-ASES/dr-lean, and a durable source checkout
exists at /Users/jjones/Documents/repos/dr-lean. This project
is separate from Analytic-Lab; the Lab contains no Lean files from this work.
