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
  its zero-or-H-stable alternative is now proved too, through positive
  directional derivatives, Gauss–Lucas and coefficientwise limits.
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
- The normalized matrix is an exact contraction in the finite sum-of-squares
  norm, and its two stationary singular-vector identities and weighted
  orthogonality equations are proved without entrywise positivity.
- The squarefree coefficient of the matrix product polynomial equals the
  permanent for every real square matrix, including dimension zero. This
  supplies the coefficient identification for capacity induction.
- **The unconditional van der Waerden permanent lower bound** for every
  doubly stochastic matrix, including dimensions zero and one. The proof
  uses the actual multivariate capacity, proved stable differentiation,
  finite variable reduction, capacity descent and coefficient identification.
  Its complete equality classification is now proved too: equality holds
  exactly at the uniform matrix, including dimensions zero and one.
  The first-deletion capacity bound and strict x log x convexity include
  unit entries and their 0^0 entropy factors.
- The finite weighted sweep bound (N-1)E/(4V), with exact sorting, ties,
  disconnected zero-energy cases and complement selection.
- The full scalar dimension transfer for n>=8, the refined n=7 scalar
  contradiction, and the exact two-block gamma-product bound, now connected
  to the actual matrix cut and permanent floor.
- Actual spectral scores, zero weighted mean, exact energy/gap identity,
  positive variance at nonuniform global maxima, and the precise
  0<=gap<=permanent/(1-delta) bound, including disconnected support.
- The entropy-derived shared subset discrepancy bound and the n=7
  marginal cap 23/20; empty/full subsets and zero cell entries are included.
- The substochastic permanent floor and the two-block floor for arbitrary
  row/column subsets of equal size, using actual transport and reindexing.
- **The complete Dittert inequality and unique equality for every n>=6.**
  The actual spectral cut, shared marginal discrepancy, capacity transport,
  equal cut cardinalities and two-block permanent floor imply the checked
  scalar contradiction. Compactness then gives the full inequality and iff
  equality on all nonnegative mass-n matrices. No support, stationarity or
  balanced-marginal assumption appears in the resulting theorem.
- The exact fourteen-vertex path Poincare certificate and its refined sweep,
  including zero energy and tied scores. This supplies the actual order-seven
  matrix argument. Order six uses the proved sharper marginal estimates,
  exact alternating path, actual singleton cell bound and permanent floor,
  and all 546 proved scalar certificate coefficients.

In progress:

- The actual polynomial/orbit identities for the small-order matrix proofs.
- The remaining square cases at orders three through five and their
  small-order matrix certificate identities.

The principal all-dimension square, K=3, K=4 and large-endpoint results remain
incomplete. Dittert is proved at orders one, two and every order at least six.
The full van der Waerden bound/equality and real-capacity
transport prerequisites are now complete in this project.
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
That square-foundation commit, `ef8d112ff651366a72a09f90e71bf5ef1e215034`,
passed [independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34363221311)
and was advanced to private main.

The capacity-bound checkpoint adds genuine stable differentiation,
permanent coefficient identification, normalized contraction, weighted
sweep and the complete n>=7 scalar stage. Its combined build passed 3,506
dependency jobs and audited 1,326 project declarations. The persistent
tests include a stable polynomial that becomes zero under differentiation
at zero, empty-matrix coefficient one, factorial multiplicity, exact sweep
sharpness and disconnected zero-energy cuts. This establishes the permanent
inequality prerequisite; its strict equality proof remains active work.

The following combined checkpoint completes permanent equality and adds
the actual spectral pair, marginal discrepancy and arbitrary-subset block
floor. All 3,515 dependency jobs passed, and 1,500 project declarations
passed the transitive standard-axiom audit. Persistent boundary tests include
the unit-entry entropy factor, strict boundary/equality separation, sparse
and empty blocks, independent noncontiguous row/column subsets, nonunit
domination scaling, and rejection of an incorrect crossing-mass factor.
The twenty-target release inventory still had only the same three completed
principal rectangular declarations at that checkpoint; the square theorem
was not yet assembled. Its exact commit `030c574e9c92d2cbda0fe2a34d1309e7b9244f7a`
passed [independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34366361102),
was advanced to private main, and was pulled into the durable source checkout.

The next development stage assembled the full n>=7 square range. Its source
map is [SPECTRAL-PROOF](SPECTRAL-PROOF.md). The all-dimension square release
target remains pending until the separate orders three through six are proved;
the completed principal-target count remains three of twenty.
The combined build passed all 3,527 dependency jobs and the transitive audit
covered 1,938 project declarations. All seven source-guard corruption controls
passed. The new tests expand the n>=7 theorem to the original matrix statement,
check the endpoint normalization, and reject omission of a crossing rectangle.
The order-six package includes all 63 cut comparisons and 546 exact Bernstein
coefficients, with positive-denominator transfer and negative controls; its
actual matrix assembly remains work in progress. An independent review of the
complete n>=7 dependency chain found no semantic issue with the energy/crossing
factors, cardinalities, zero cases or compactness-derived equality claim.
That exact commit `76546a5688e8e902e44eec4ccebd0d1dcdd7ea93` passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34369034229),
was advanced to private main, and was pulled into the durable source checkout.

The following stage completes order six on the full closed simplex, including
unique equality. The alternating path is proved by exact rational Gram bounds,
strict Schur algebra, and a finite Cauchy-Schwarz transfer to the mean-zero
vertex range. Minimizing over all even proper prefixes directly proves the
cut bound; its strict upper bound forces balance. Choosing the smaller
cardinality side preserves the singleton extremal orientation. These two
simplifications remove a separate ordinary-path certificate and a volume
rounding step from the source proof without weakening its conclusion.
The actual matrix proof retains the distinguished singleton cell and applies
the two scalar permanent comparisons to the same selected cut. The principal
all-dimension target remains pending at orders four and five.

Order three is now complete on the full nonnegative mass-three simplex.
The support argument proves its Boolean exhaustion by ordinary kernel
reduction, handles all canonical boundary faces, and reduces positive
maximizers to uniform by three exact column blends. All 86 public
order-three declarations passed the standard-axiom audit. The equivalent
3-by-3 probability endpoint is also proved, with value 32/81 and unique
equality. This is the established small Dittert case used as a prerequisite;
it does not by itself prove arbitrary rectangular K=3. The source map is
[ORDER-THREE-PROOF](ORDER-THREE-PROOF.md).

The ten-vertex alternating path and even-prefix sweep have also been proved
for use at order five. Their constants come from exact rational Gram bounds;
paired tied-score zero-energy cases and a false stronger constant are covered
by persistent controls. Order five still requires its actual marginal and
permanent estimates, so this dependency is not recorded as its matrix theorem.

The combined order-three/order-six checkpoint passed all 3,553 dependency
jobs and audited 2,752 project declarations transitively against the standard
axiom allowlist. Persistent tests expand both the original mass-three formula
and the complete n>=6 statement, including the exact unique equality case.

Working checkout during initial development: /private/tmp/dr-lean. The private
remote is https://github.com/JD-Jones-ASES/dr-lean, and a durable source checkout
exists at /Users/jjones/Documents/repos/dr-lean. This project
is separate from Analytic-Lab; the Lab contains no Lean files from this work.
