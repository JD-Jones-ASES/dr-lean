# Square Dittert: formalization dependency audit

Read-only audit, 2026-09-09. Source mathematics: Analytic-Lab P0174
`SQUARE_SPINOUT_AUDIT.md`, `SPECTRAL_SQUARE_ENDPOINT.md`, and the order-four
certificate contract. Library inspected: gn-lean's pinned Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, Lean `v4.33.0`.
No foreign proof implementation was read or copied. All paths below are
relative to that Mathlib checkout. Names were checked in source; 32 representative
declarations were also checked by compiling `/private/tmp/DRSquareDependencyChecks.lean`
with `lake env lean` in the initialized dr-lean repository (exit 0; output
`/private/tmp/dr-square-dependency-checks.log`). This audit does not claim to
have compiled a complete square proof.

## Current completion update

The initial inventory below describes what the pinned library supplies.
The project has since proved the exact normalization, Dittert orders one
and two, the listed finite permanent identities, and the complete finite
real-capacity transport criterion in `DR/Square/Transport.lean`.
Transport sufficiency uses compact maximization followed by a secondary
row-energy minimization and a deficient-cut contradiction. Both the cut
criterion and doubly stochastic domination are unconditional compiled
theorems. Van der Waerden with equality remains a missing prerequisite.

## Library audit conclusion

The square alternative proof is a substantial new formalization project.
Mathlib contains the permanent definition, matrix algebra, finite-dimensional
analysis, and Birkhoff decomposition. It does **not** contain the van der
Waerden permanent lower bound or its equality case, nor a finite real-capacity
max-flow/min-cut theorem. These are actual proof obligations. A citation,
an axiom, a theorem taking these facts as hypotheses, or passing the rational
certificate checks cannot complete the requested unconditional square theorem.

The general square proof need not formalize an abstract Cheeger theorem or
invoke the full spectral theorem: KKT constructs the precise eigenvector used,
and the sweep proof can be written directly with finite sums and a sorting
permutation. This is a useful reduction in engineering scope without weakening
the mathematics.

## Existing library inventory

| Needed input | Existing definitions or theorem names | File and application limit |
|---|---|---|
| Permanent | `Matrix.permanent`; `Matrix.permanent_transpose`; `Matrix.permanent_permute_cols`; `Matrix.permanent_permute_rows`; `Matrix.permanent_smul`; `Matrix.permanent_updateCol_smul`; `Matrix.permanent_updateRow_smul` | `LinearAlgebra/Matrix/Permanent.lean`, lines 32–112. Definition sums `prod i, M (σ i) i`; account for this orientation. No minor/Laplace expansion, monotonicity, nonnegativity or derivative API in that file. |
| Doubly stochastic matrices | `doublyStochastic`; `mem_doublyStochastic_iff_sum`; `sum_row_of_mem_doublyStochastic`; `sum_col_of_mem_doublyStochastic`; `nonneg_of_mem_doublyStochastic`; `transpose_mem_doublyStochastic_iff`; `reindex_mem_doublyStochastic`; `exists_mem_doublyStochastic_eq_smul_iff` | `Analysis/Convex/DoublyStochasticMatrix.lean`, lines 42–167. These declarations are in the root namespace, not `Matrix`. |
| Birkhoff | `exists_eq_sum_perm_of_mem_doublyStochastic`; `doublyStochastic_eq_convexHull_permMatrix` | `Analysis/Convex/Birkhoff.lean`, lines 148,166. Gives a convex combination of permutation matrices, **not** a permanent lower bound. Permanent is not convex, so this does not prove van der Waerden. |
| Doubly stochastic operator norm | `Matrix.l2_opNorm_le_one_of_mem_doublyStochastic` | `Analysis/Convex/Birkhoff.lean:204`. Does not directly apply to the normalized KKT matrix T, which is generally not doubly stochastic. Prove the weighted Cauchy–Schwarz contraction directly. |
| Finite Hall | `Finset.all_card_le_biUnion_card_iff_exists_injective`; `Fintype.all_card_le_rel_image_card_iff_exists_injective`; `Fintype.all_card_le_filter_rel_iff_exists_injective` | `Combinatorics/Hall/Basic.lean`, lines 116,176,198. Useful for support matching. Hall alone does not supply the quantitative capacity domination used in the square proof. |
| Cone separation / Farkas | `ProperCone.hyperplane_separation_point`; `ProperCone.hyperplane_separation'`; `ProperCone.relative_hyperplane_separation` | `Analysis/Convex/Cone/Dual.lean` and `InnerDual.lean`. Potential transport construction route. Beware that the proper-cone map uses closure: a direct finite-capacity feasibility proof still needs exact attainment. |
| Compact maximum | `IsCompact.exists_isMaxOn`; `ContinuousOn.exists_isMaxOn'` | `Topology/Order/Compact.lean`, lines 248,267. Apply to the finite nonnegative fixed-mass simplex and continuous polynomial objective. |
| Boundary first order conditions | `IsLocalMaxOn.hasFDerivWithinAt_nonpos`; `IsLocalMaxOn.hasFDerivWithinAt_eq_zero`; `IsLocalMax.hasDerivAt_eq_zero` | `Analysis/Calculus/LocalExtr/Basic.lean`, lines 104,126,247. An explicit two-cell mass-transfer curve may be shorter than a general KKT framework. Only supported-cell equality is legitimate. |
| AM–GM and exact equality | `Real.geom_mean_le_arith_mean_weighted`; `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`; `Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg` | `Analysis/MeanInequalities.lean`, lines 130,266,279. Use uniform positive weights for marginal product ≤1 and equality; apply within complementary subsets for entropy grouping. |
| Cauchy–Schwarz finite sums | `Finset.sum_mul_sq_le_sq_mul_sq`; `Finset.sq_sum_div_le_sum_sq_div`; `Finset.sum_sq_le_sq_sum_of_nonneg` | `Algebra/Order/BigOperators/Ring/Finset.lean`, lines 159,169,35. Handles normalized matrix contraction, shared-deficit budget, sorted-gap inequalities. |
| Log estimates | `Real.log_le_sub_one_of_pos`; `Real.log_le_log`; `Real.log_le_log_iff` | `Analysis/SpecialFunctions/Log/Basic.lean`, lines 307,151,147. Reciprocals give `-log(1-rho) ≤ rho/(1-rho)`. |
| Entropy calculus | `Real.binEntropy`; `Real.hasDerivAt_binEntropy`; `Real.deriv2_binEntropy`; `Real.strictConcave_binEntropy` | `Analysis/SpecialFunctions/BinaryEntropy.lean`, lines 61,257,360,443. Shannon binary entropy is not the two-parameter binary relative entropy in P0174. Derive the required two-parameter estimate directly. |
| General KL | `InformationTheory.klDiv` and Gibbs/data-processing declarations in that namespace | `InformationTheory/KullbackLeibler/Basic.lean`, `DataProcessing.lean`. Measure-theoretic framework is likely more expensive than the elementary binary derivative proof here. No Pinsker theorem found by a whole-library source search. |
| Popoviciu | `ProbabilityTheory.variance_le_sq_of_bounded` | `Probability/Moments/Variance.lean:500`. A finite-weight direct proof avoids constructing a probability measure for the sweep. |
| Sorting | `Finset.sort`, `Finset.pairwise_sort`, `Finset.sort_nodup`, `Finset.mem_sort`, `Finset.length_sort`, `Finset.orderEmbOfFin` | `Data/Finset/Sort.lean`. For ties, sort vertices by `(score,index)` so cardinality is retained, or use a total preorder on vertex scores with stable tie-breaking. |
| Spectral theory if useful | `Matrix.IsHermitian.eigenvectorBasis`; `Matrix.IsHermitian.mulVec_eigenvectorBasis`; `Matrix.isSymmetric_toEuclideanLin_iff` | `Analysis/Matrix/Spectrum.lean` and `Hermitian.lean`. Available but not required for the explicit KKT eigenpair route. |
| Rational PSD witnesses | `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`; `Matrix.posSemidef_iff_dotProduct_mulVec` | `LinearAlgebra/Matrix/PosDef.lean`, lines 308,298. Reconstruct a rational LDL factorization, verify matrix identities exactly, and derive the real quadratic-form bound. No trust in an external LDL verdict. |
| Bernstein positivity | `bernstein_nonneg`; `bernstein.probability`; `bernsteinPolynomial`; `bernsteinPolynomial.sum` | `Analysis/SpecialFunctions/Bernstein.lean`, lines 71,109; `RingTheory/Polynomial/Bernstein.lean`, line 273. Existing basis nonnegativity/partition identity supports a tiny local scalar and tensor certificate lemma. |

## New prerequisites, precisely

1. **Permanent API.** Nonnegative/monotone, rectangular minor indexing,
   Laplace expansion, block-diagonal contribution lower bound, continuity,
   polynomial derivative, and the constant-matrix evaluation. These are finite
   combinatorial proofs from `Matrix.permanent`, not difficult analysis.
2. **Van der Waerden including equality.** For `0<n`, nonnegative n-square B
   with every marginal one: `n!/(n:ℝ)^n ≤ B.permanent`. For `2≤n`, equality
   iff every entry is `1/n`. Both parts are used: domination needs the bound;
   zero-deficit and zero-score branches need equality. Whole-library searches
   for permanent, van der Waerden, Gurvits, real stability and hyperbolicity
   found no theorem solving this dependency. The van der Waerden theorem in
   `Combinatorics/HalesJewett.lean` is the arithmetic-progression theorem.
3. **Exact finite capacity transport.** If A is nonnegative and every row set I,
   column set J satisfies `A(I,J) ≥ |I|+|J|-n`, produce a doubly stochastic B
   with `B≤A`. This specializes the required max-flow theorem. A compact
   maximal feasible flow plus finite residual reachability proof works for real
   capacities and avoids false assumptions about Ford–Fulkerson termination.
   Alternatively derive the exact polytope separation theorem from Farkas and
   prove its dual reduces to these cuts. This is medium/large formal work.
4. **Binary discrepancy.** Grouped AM–GM and the elementary derivative proof of
   `D(p||q) ≥ 2(q-p)^2` on `0<p,q<1`, with empty/full subset cases separate.
   Preserve the common deficit `rho+sigma≤delta` when combining margins.
5. **Stationary sweep.** Supported-cell derivative equality; row/column
   expansion; explicit singular pair; contraction; zero weighted mean; exact
   energy identity; sorted-gap cut estimate; complement-volume normalization.
   New finite lemmas needed; abstract existence of an eigenbasis is irrelevant.
6. **Certificates with semantic bridges.** Rational Bernstein coefficient
   positivity alone is insufficient. Prove (a) the polynomial identity after
   denominator clearing, (b) denominator positivity on the physical domain,
   (c) basis nonnegativity and partition of unity, and (d) parameter domain
   membership. For n=4 additionally prove complete 16-variable polynomial
   identity, every physical multiplier's PSD bound, and the stability/equality
   deduction. Do not narrow to the 224 orbit representatives without a proved
   orbit-cover/symmetry lemma or an exhaustive kernel-checked identity.
7. **Infinite dimension transfer.** Prove gamma ratio monotonicity, endpoint
   minimum of `gamma_s*gamma_(n-s)`, monotonicity of `n*a_n,n*b_n`, and of
   `(1-x/n)^n` for the specified domains. Checking finitely many n cannot
   replace these steps.

## Smallest honest implementation order

1. Fix the actual public challenge predicates: all nonnegative square matrices,
   total mass n, unique uniform equality; inclusive-OR probability definition,
   not an inequality supplied as a field in an input structure. Prove the
   normalization bridge `F_n(P)=gamma_n*Phi(nP)` and elementary n=2 theorem.
2. Build the permanent finite API, simplex compactness/first-order lemmas and
   general rational Bernstein/PSD certificate correctness layers. They serve
   square and rectangular work in parallel.
3. Start van der Waerden/equality early as a separate foundational module;
   start specialized capacity transport independently. These are the critical
   path. A published Gurvits capacity proof is a possible candidate, **not a
   ready Mathlib theorem**: it requires the appropriate multivariate real
   stability/derivative-specialization closure and equality analysis. Current
   univariate helpers include `Polynomial.Splits.eval_derivative_div_eval_of_ne_zero`,
   `Polynomial.card_roots_le_derivative`, and complex Gauss–Lucas in
   `Analysis/Complex/Polynomial/GaussLucas.lean`; those do not by themselves
   close the multivariate argument. Select and audit the full source proof
   before committing to that foundation route.
4. Formalize the general stationary/entropy/sweep/near-block lemmas, then n≥7
   scalar bases and dimension transfer. This completes the infinite square
   branch once item 3 is proved; it has no n=5 or n=6 dependency.
5. Formalize n=3 from the endpoint-only support chain (use the audited
   `6ab≤3/8<32/81` shortcut to omit general matching positivity), and n=4 from
   the local full physical certificate. This can run alongside item 4.
6. Formalize the alternating balanced sweep and n=6 proof. It does not depend
   on smaller Dittert inequalities. Formalize n=5 last because it explicitly
   invokes n=2,3,4 on actual blocks.
7. Assemble every n≥2 and the exact equality conclusion. Only then expose the
   unconditional square theorem through `Solution.lean`/the registry comparator.
   Intermediate modules may prove reusable implication lemmas, but they are
   not replacements for the requested final unconditional theorem.

This order preserves the complete requested result. It does not promise a
time estimate or suggest that passing a small initial scaffold is a
publication gate.
