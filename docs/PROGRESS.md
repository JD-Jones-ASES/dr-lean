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
- The full polynomial capacity bridge for split real polynomials, including
  all zero and degree-padding cases. The actual matrix polynomial is proved
  homogeneous, coefficientwise nonnegative, H-stable and of capacity one.
- Actual conditional occupation identities, including the diagonal term,
  centered quadratic bound and exact rational constants. All conditional
  collision controls are derived from the actual sampling law; the positive
  kernel theorem has only explicit marginal and variance hypotheses.
- Column-deletion mass and variance estimates: every sufficiently large-board
  contender meets the normalized deletion hypotheses for every column pair.
- Exact iid homogeneity and invariance of conditional occupation under
  nonzero scaling; the general factorial-normalized rook decomposition.
- A compactness/transpose closure lemma: column rigidity in both orientations
  implies the sharp uniform inequality and unique equality.
- The exact two-column blend identity, including its factorial factor and
  occupation-kernel interpretation, for the actual iid objective.
- **The complete all-order large-board theorem and its K^21 corollary.**
  Both principal statements conclude the full sharp inequality and unique
  equality on the closed probability simplex with independent dimension
  lower bounds. Positivity, concentration and rigidity are proved internally.
  An independent semantic/type/axiom review found no scope weakening.
- Positive one-variable slices of homogeneous H-stable polynomials split
  over the reals with nonpositive roots. Gurvits's norm comparison is proved
  for homogeneous H-stable real polynomials without a coefficient-sign
  restriction.
- Coefficientwise limit closure preserves homogeneity, nonnegative
  coefficients and the zero-or-H-stable alternative in finitely many
  variables. Differentiation at zero preserves degree and coefficient signs;
  its H-stability is still being proved.
- Exact rational tensor Bernstein and Gram/LDL certificate soundness,
  including closed-box boundaries, zero pivots, singular kernels and positive
  denominator obligations. Lean rejects corrupted identities and margins.
- All 47 rational Bernstein coefficients and the exact scalar gap identities
  at n=7 and n=8. These are complete scalar base obligations, not the full
  square matrix theorem.
- The two square stationarity equations follow from feasible exponential
  row and column scaling. The proof preserves arbitrary zero support.
  Marginal positivity and the shared permanent-deficit budget are derived
  from comparison to the uniform value, so the global-maximizer equations
  have no additional support or marginal assumptions.

In progress:

- Van der Waerden's permanent lower bound and equality prerequisites.
- The actual polynomial/orbit identities for the small-order matrix proofs.
- The spectral dimension transfer, weighted sweep and remaining small-order
  matrix certificate identities.

The principal square, K=3, K=4 and large-endpoint results remain
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
That checkpoint, `de80dde73014a0144321ba2f0cdc596d416d95c2`, also passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34358562072)
and was advanced to private main.

The following combined local build adds occupation moments and bounds,
normalized deletion, scaling, rook decomposition, maximizer closure and
the polynomial/stability foundations: all 3,248 dependency jobs passed,
and 718 project declarations passed the transitive axiom audit. Source
guards, their seven corruption controls, and semantic/boundary tests passed.
Its exact commit `b3797cd3c16d253deb92542916e3598849fb037f` passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34360127140).

The all-order proof simplifies the Lab's final uniqueness argument: the exact
blend identity forces identical columns at an actual global maximum; applying
the same argument to the transpose forces identical rows. Total mass then
determines the uniform matrix directly. This avoids a separate final
product-distribution/Maclaurin step without changing the scope or constants.
It does not imply the square sampling endpoint K=M=N, where the dimension
threshold is not met.

The combined all-order checkpoint passed all 3,464 dependency jobs and the
transitive audit of 880 project declarations. The new scope tests expose
both principal results as inequalities and iff equality statements on all
nonnegative mass-one real matrices, and include the exact D_4 dimension
boundary. Source guards and their seven corruption controls passed. These
development checks complete three of the twenty required release targets;
the complete release gate remains pending.
That exact all-order commit, `ca62b079af2be280c2ffc4b8bb56c1d4761ebe18`, passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34361456001),
was advanced to private main, and was pulled into the durable source checkout.

The subsequent square-foundation checkpoint passed all 3,492 dependency
jobs and audited 1,101 project declarations. It includes the stationary
pair, closed-simplex contender bounds, homogeneous limit closure, both
certificate soundness layers and the n=7/n=8 scalar bases. Persistent tests
cover singular Gram matrices, zero pivots, empty dimensions, exact kernel
lifting, rejected matrix mutations, corrupted Bernstein identities and
inflated coefficient margins. None of the seventeen pending principal
release targets is marked complete by these dependency proofs.

Working checkout during initial development: /private/tmp/dr-lean. The private
remote is https://github.com/JD-Jones-ASES/dr-lean, and a durable source checkout
exists at /Users/jjones/Documents/repos/dr-lean. This project
is separate from Analytic-Lab; the Lab contains no Lean files from this work.
