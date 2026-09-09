# Current formalization state

Updated 2026-09-09. The complete release goal remains active.

The latest verified inputs include the actual full-simplex four-row collision
remainder, corrected-minorant boundary families, the four-row K=3 leading
gauge bound, and the finite-certificate ordinary-column matrix reduction.
See [FOUR-ROW-INPUTS](FOUR-ROW-INPUTS.md) for exact hypotheses and outstanding
obligations. The principal target count remains four of twenty.

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

The complete K=3 inequality and unique equality are also proved whenever
both dimensions are at least ten, and on the five-through-nine-row infinite
strips listed in [ORDER-THREE-RANGES](ORDER-THREE-RANGES.md), in both
orientations. The remaining small-side and finite cases still prevent
completion of the all-rectangle K=3 release target.

The complete square Dittert theorem is now proved for every n>=1, including
unique equality on the full nonnegative mass-n domain. The order-four sextic
identity and complete physical orbit coverage are connected to the actual
probability; the order-five literal singleton numerator is connected to all
proved Bernstein bounds and the actual deletion minor. Read
[ORDER-FOUR-PROOF](ORDER-FOUR-PROOF.md) and [ORDER-FIVE-PROOF](ORDER-FIVE-PROOF.md).
The all-order wrapper is `DittertRybin.dittert_unique_maximum`.

For K=3, positive global maximizers are now proved to be the original uniform
board for all independent M,N>=3. Exact cubic interpolation and strict local
uniqueness close this argument. Boundary-support classification remains active.

The complete three-row family now proves `UniformMaximizer 3 N 3` for every
N>=3 and its transpose, including all boundary supports and exact equality.
[The three-row proof](THREE-ROW-PROOF.md) describes the complete support
classification. The four-row scalar gauge bound and unique uniform equality
are proved by an exact sorted-gap certificate. Actual endpoint contender
normalization, variance, column caps, and separate original/deleted row laws
are complete prerequisites. [The rectangular foundation map](RECTANGULAR-FOUNDATIONS.md)
states the remaining interfaces and obligations.

The principal K=3, K=4 and large-endpoint release targets remain incomplete.
Four of the twenty required principal targets are now proved locally.
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

That exact order-three/order-six commit
`77776c3de0d8b526dfab2ea48f7f8f97e5a824a4` passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34373242711),
was advanced to private main, and was pulled into the durable source checkout.

The following small-order foundation stage adds the complete order-four
seed-matrix layer: all 8,448 canonical entries, 33 exact Gram identities,
and 495 positive principal pivots pass ordinary kernel checks. The actual
formula-defined seeds satisfy the 1/10 centered quadratic bound and have
exactly the constant nullspace. The sextic identity and multiplier-orbit
coverage were separate remaining obligations before the order-four matrix
theorem can be claimed. Closed seed checks are cached in separate modules
so their finite computations can be replayed efficiently.

Order five now has its actual stationary marginal envelope, proved with a
three-step bootstrap on the full closed domain, and all 67 scalar guard
coefficients. The energy lower sign retains the physical deficit bound;
its rational interval endpoint alone would give a negative energy and is
explicitly tested. A reusable exact power-to-Bernstein conversion and affine
coefficient transformation are proved over rational algebras, allowing later
large certificates to use finite rational coefficient checks. Their tests
cover degree zero, degree elevation, affine scaling and closed endpoints.
The combined foundation build passed 3,566 dependency jobs and audited 4,524
project declarations. It does not complete another principal release target.

The next combined stage completes actual row/column-permutation coverage of
all 3,876 quartic multiplier matrices by the 33 proved seeds. Every multiplier
therefore satisfies the quantitative centered bound. The order-four sextic
identity remains pending. Order five adds all 30 derivative coefficients and
500 two-block scalar coefficients, with their exact gap and positive-floor
consequences on the closed triangular domain.

For rectangular K=3, the cubic failure polynomial is now proved equal to the
actual ordered sampling event, including repeated cells and all six ordered
L-shaped cases. The identity holds for signed weights; its probability
corollary covers every nonnegative mass-one matrix. The exact dimension
criterion is positive for min(M,N)>=10 and the stated six-through-nine-row
strips; the matrix estimates connecting that criterion to the full maximum
are a separate next stage. Tests retain false adjacent thresholds and the
signed, repeated-cell, nonunit-mass and L-shape cases.

This combined build passed all 3,585 dependency jobs and audited 5,463
project declarations transitively. Source guards and their seven corruption
controls passed. These are development foundations: the principal-target
count remains three of twenty, and the repository remains private.

That small-order/cubic-identity checkpoint,
`68e64d0de5229ca235ffcf3030738044a683542a`, passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34377314242)
and was advanced to private main. Its fresh CI build took about 38 minutes.
The development job limit is increased to 120 minutes for the next larger
certificate package; all proof, source and axiom checks remain required.

The next combined checkpoint connects the actual cubic probability identity
to the complete large-range and infinite-strip K=3 theorems. The centered
expansion, orthogonal energy decomposition, mixed Cauchy bound and near/far
estimates all hold on the closed probability simplex. For five rows and
N>=121, the exact near-region margin is 27197/2772275; zero cell entries,
zero row deviation and zero total centered energy remain covered.

Order five now has its actual balanced spectral cut of cardinality one or
two, preserving complete cross-subset marginal ordering, subset mass signs
and singleton extrema. Homogeneous lower-order Dittert bounds include
arbitrary nonnegative block mass and the zero-mass boundary. All 18,648
rational singleton interval coefficient bounds and all 56 two-axis
coefficient conversions pass ordinary kernel checks. The separate identity
from the literal source numerator to its power table remains pending, so
these checked data are not yet claimed as the completed singleton inequality.

This combined build passed all 3,685 dependency jobs and audited 8,571
project declarations against the standard-axiom allowlist. Persistent tests
cover the actual K=3 ranges and their transposes, boundary supports, exact
mixed-term constants, five-row margin, zero-mass scaling, and the degenerate
singleton coordinate box. The complete-release target count stays at three
of twenty. That exact checkpoint,
`71ab5fb1e4bae27fbd43f26ab06f2e1646750836`, subsequently passed
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34382115147)
and was advanced to private main and the durable source checkout.

The full-square checkpoint adds the complete order-four certificate and
order-five assembly. All 86 sparse arithmetic equalities identify the literal
singleton numerator, all 56 coefficient transformations and 18,648 coefficient
bounds apply to it, and the resulting actual matrix argument closes order five.
The final order-five/all-order replay passed 3,677 dependency jobs; all seven
stored final axiom audits contain only the standard three axioms. Sparse
arithmetic uses a proved finite-fuel list merge and a proved zero filter,
including arbitrary unsorted inputs and zero tensor entries. Deterministic
reproduction agrees with all fourteen generated arithmetic-stage files.

The additional K=3 support work derives full-simplex KKT equations, exact
same-support averaging and a common support normal form; rules out empty
rows and columns at maxima; proves signed cubic gradients and interpolation;
and proves original-matrix uniqueness for every positive global maximizer.
Proper doubleton support conditions retain zero residuals and the exact singular
equality case. These are dependencies for the still-open all-rectangle K=3
release target. The combined full-square build passed all 3,781 dependency jobs and audited
11,359 project declarations transitively against the standard-axiom allowlist.
All seven source-guard corruption controls, the exact four-of-twenty target
inventory, forty-one relative documentation links, and whitespace checks passed.
Independent CI for this full-square checkpoint is still required.

The next rectangular foundation checkpoint adds the actual singleton exclusion,
existence of a full column, and exclusion of all three doubleton types at a
three-row global maximum. Its single-doubleton scalar proof keeps all four
KKT conditions and strict integer borders. The four-row polynomial kernel is
identified with the actual sampling kernel, including factor 24 and full-simplex
pair rigidity under the stated concentration bounds. The closed-domain
Newton--Maclaurin, exact variance, row-assignment, and factorial-decay modules
supply common endpoint prerequisites; none assumes an endpoint conclusion.

This combined checkpoint passed all 3,819 dependency jobs and audited 11,699
project declarations transitively against the standard-axiom allowlist.
Persistent tests include actual support boundaries, zero residuals, signed
sampling formulas, row-normalization and factorial controls, repeated roots,
and the nonunique first-order case. All seven source-guard corruption tests
passed. The principal-target count remains four of twenty; full-square CI and
independent CI for this subsequent checkpoint remain separate required gates.
See [RECTANGULAR-FOUNDATIONS](RECTANGULAR-FOUNDATIONS.md) for readable proof
interfaces and exact remaining obligations.

The following checkpoint completes the entire three-row K=3 family and its
transpose. Every zero-support class is excluded from an actual global maximum;
compactness and the positive-matrix theorem give the full sharp inequality and
unique equality. The N=2 countercontrol confirms the dimension guard. Independent
semantic review checked the all-column two-doubleton argument, normalization,
residual positivity and final equality scope.

It also proves the four-row scalar gauge gap and exact equality via the
homogeneous sorted-gap certificate, with deterministic source reproduction.
The actual contender initial cap and the concentration/deletion assembly have
independent semantic review; the corrected leading minorant and collision
remainder remain explicit obligations. Endpoint normalization and caps now use
actual original-row probabilities and a distinct deleted-row law. One duplicated
endpoint lemma name was mechanically renamed during combined integration;
all affected proofs and tests were replayed successfully.

The combined build passed all 3,845 dependency jobs and audited 12,020 project
declarations transitively against the standard-axiom allowlist. Source guards,
generator reproduction, Python compilation, the twenty-target inventory and
documentation/whitespace checks passed. Four principal targets remain proved;
completing three rows does not yet complete the all-rectangle K=3 target.
The preceding rectangular-foundation commit is
`bdd1db2fd8861b01063cbdb6f62c6662b1b66cd3`, with
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34390255947)
still running. Independent CI remains required for this subsequent checkpoint.

The next collision/block checkpoint passed all 3,905 dependency jobs and
audited 12,448 project declarations transitively against the standard-axiom
allowlist. Independent semantic review checked the actual event restriction,
all sampling factors, the corrected minorant's closed boundary families and
coefficient coverage, and the K=3 copositive-to-probability bridge. The exact
42,875-coefficient generator reproduces. The ordinary-column block reduction
also includes PSD and exact constant-kernel transfer; its denominator and
strict-positive-block negative controls pass. Independent CI remains required.
The preceding three-row/gauge commit is
`486d70d7bdf148cc88cbcfa32c6c61288478854a`, with
[independent CI](https://github.com/JD-Jones-ASES/dr-lean/actions/runs/34392339329)
still running. None of these inputs is counted as a completed new principal target.

Working checkout during initial development: /private/tmp/dr-lean. The private
remote is https://github.com/JD-Jones-ASES/dr-lean, and a durable source checkout
exists at /Users/jjones/Documents/repos/dr-lean. This project
is separate from Analytic-Lab; the Lab contains no Lean files from this work.
