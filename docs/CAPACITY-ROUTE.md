# Capacity route for the full square permanent prerequisite

Status: bounded formalization checkpoint, 2026-09-09. The van der Waerden
inequality and its equality characterization are not yet formalized here.
This is a plan for proving them, not an assumption or conditional replacement.

Later completion update: `CapacityPolynomial.lean` now proves the full
split-polynomial bridge, including nonpositive roots derived from
coefficient signs, multiplicities and degree padding. `CapacityStability.lean`
defines actual complex half-plane nonvanishing and proves the initial
matrix polynomial is homogeneous, coefficientwise nonnegative, H-stable
and of capacity one. The initial-checkpoint inventory below is preserved;
its former missing root bridge and initial stability steps are now complete.
`StableSlices.lean` now supplies positive-slice splitting, and
`NormComparison.lean` proves Gurvits's norm comparison for homogeneous
H-stable real polynomials. The remaining frontier is derivative and boundary
specialization closure, capacity descent, coefficient identification and
matrix equality. See [PROGRESS](PROGRESS.md) for the current checkpoint.

## Primary sources and selected route

1. Leonid Gurvits, *Van der Waerden/Schrijver–Valiant like conjectures and
   stable (aka hyperbolic) homogeneous polynomials: one theorem for all*,
   Electronic Journal of Combinatorics 15 (2008), R66, arXiv:0711.3496v2.
   Official source: https://arxiv.org/abs/0711.3496v2;
   PDF: https://arxiv.org/pdf/0711.3496.
   Use Lemma 3.2 for the univariate capacity step, Section 4 for homogeneous
   stability and differentiation/specialization closure, and Theorem 4.10
   for the capacity induction. The useful factor is
   G(k)=((k-1)/k)^(k-1), with G(1)=1.

2. Monique Laurent and Alexander Schrijver, *On Leonid Gurvits' proof for
   permanents*, American Mathematical Monthly 117(10) (2010), 903–911,
   DOI:10.4169/000298910X523380.
   Official author-institution record: https://ir.cwi.nl/pub/16667;
   PDF: https://ir.cwi.nl/pub/16667/16667A.pdf.
   Use the matrix-specific equality argument in Corollary 1(d), pp. 909–910.
   It avoids Gurvits's more general Gårding/hyperbolic-cone equality argument.

For a doubly stochastic A, form p(x)=prod_i sum_j A_ij x_j. Its capacity
is 1 by weighted AM–GM and evaluation at the vector of ones. Repeatedly
differentiate one variable and set it to zero. Stability supplies a
nonnegative real-root factorization for each positive slice, and the
univariate estimate supplies the sharp capacity loss. The product of
the losses is n!/n^n; the final mixed derivative is the permanent.

For equality, Laurent–Schrijver bound the capacity after the first
derivative by prod_i (1-A_in)^(1-A_in), then by G(n). Strict convexity
of x log x forces the last-column entries to be equal. Repeat with each
column. The proof must explicitly allow A_in=0 or 1; a displayed quotient
by 1-A_in cannot be used in the zero-weight case.

### Boundary correction when reading the sources

Gurvits Lemma 3.2's printed univariate equality characterization needs a
positive-capacity restriction. For Q(t)=t^2, both Q'(0) and capacity are
zero, so equality holds despite roots at zero. Our proved inequality
includes this boundary. No unrestricted equality characterization is
copied from that statement. In the doubly stochastic application the
initial capacity is 1, so the positive-capacity case is the relevant one.
The Q(t)=t^2 zero-capacity equality was independently replayed in Lean in
`/private/tmp/DRCapacityBoundary.lean`.

## Actual Lean increment

`DR/Square/CapacityUnivariate.lean` proves:

- The capacity as an actual infimum over t>0, with upper/lower bound lemmas.
- Finite AM–GM in the form prod z_i <= (sum z_i/n)^n.
- The derivative at zero of prod_i(1+a_i t), and the sharp capacity bound
  G(n) cap <= sum a_i = the actual derivative, for n>=2 and a_i>=0.
- The explicit positive comparison point n/(sum(a_i)*(n-1)); no infimum
  attainment assumption enters the argument.
- The all-zero-slope case (constant polynomial) and nonnegative scaling.
- If f(0)=0 and f is nonnegative on the positive half-line, then its
  capacity is at most its actual right derivative, when the derivative exists.
- `affineProduct_capacity_le_deriv`: for a_i,b_i>=0, n>=2,
  G(n) cap(prod_i(b_i+a_i t)) <= deriv(prod_i(b_i+a_i t),0).
  This includes zero roots, zero slopes, missing degree, and the identically
  zero product. It does not assume a stability theorem or permanent bound.
- The homogeneous linear endpoint has capacity equal to its coefficient.

`DR/Square/CapacityMatrix.lean` proves:

- Multivariate capacity as the actual infimum over all positive vectors,
  with the coordinate product denominator and explicit upper/lower bounds.
- `prod_le_matrixProduct_of_doublyStochastic`: the weighted AM–GM
  pointwise inequality for the product of a matrix's row linear forms.
- `matrixProduct_capacity_eq_one`: exact capacity one for every doubly
  stochastic matrix, including zero entries and n=0.
- `prod_capacityFactor`: prod_{k=0}^{n-1} G(k+1) = n!/n^n, including n=0.

The standalone `lake build DR.Square.CapacityMatrix` passed cleanly under
Lean v4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d (3153 jobs).
All 28 theorem declarations were inspected with `#print axioms` using
`/private/tmp/DRCapacityAxioms.lean`; each depends only on `propext`,
`Classical.choice`, and `Quot.sound`. No placeholder, added axiom, unsafe
code, or native decision procedure occurs in these modules.
The root/factorization bridge
from a `Polynomial ℝ` has not been written yet; the current input is an
explicit finite affine-factor representation.

## Available Mathlib components

- `Real.geom_mean_le_arith_mean_weighted`, and the equality theorems
  `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos` and `_of_nonneg`:
  `Mathlib/Analysis/MeanInequalities.lean`.
- `Real.strictConvexOn_mul_log` on the closed set `Ici 0`, plus
  `Real.continuous_mul_log`:
  `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`.
  Thus x log x at zero is already handled by the library.
- `Polynomial.Splits.eq_prod_roots`, `.eval_eq_prod_roots`,
  `.eval_derivative_div_eval_of_ne_zero`:
  `Mathlib/Algebra/Polynomial/Splits.lean`.
- `Polynomial.eq_centerMass_of_eval_derivative_eq_zero` and
  `Polynomial.rootSet_derivative_subset_convexHull_rootSet`:
  `Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean`.
- `MvPolynomial.IsHomogeneous.pderiv` and `.sum_X_mul_pderiv`:
  `Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean`.
- `MvPolynomial.IsHomogeneous.eval₂` and `.aeval`:
  `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`.
- Standard `MvPolynomial` evaluation, partial derivatives, coefficient
  extraction, finite products, and polynomial splits/root multiplicities.

No ready declaration for multivariate real/H-stability or its derivative
and boundary-specialization closure was found in the pinned Mathlib.
No van der Waerden lower bound or equality theorem was found.
The 13 named root, homogeneous-polynomial, and convexity APIs were checked
against the pinned environment using `/private/tmp/DRCapacityLibraryChecks.lean`.

## Remaining proof obligations in an honest implementation order

1. Initial normalization: completed in `CapacityMatrix.lean`.
2. Polynomial bridge: turn a split real polynomial with nonnegative
   coefficients and nonpositive roots into the proved affine product form,
   including degree 0/1 and zero polynomial cases. Relate functional
   derivatives to polynomial derivatives. If the actual slice degree is
   smaller than the variable count, pad with constant-one factors (zero
   slopes), already allowed by our lemma; no monotonicity proof for G(k)
   is needed for this route.
3. Define homogeneous H-stability (nonvanishing when every complex
   coordinate has positive real part), coefficient nonnegativity, and
   variable deletion/specialization. Prove the initial matrix product is
   H-stable directly from positivity of each row linear form.
4. Prove slice/root properties and closure. A faithful Gurvits Section 4
   route needs the homogeneous positive-direction root characterization,
   the norm comparison |p(z)|>=|p(Re z)|, coefficient-limit preservation,
   and derivative-plus-zero-specialization preservation. Mathlib's
   Gauss–Lucas theorem is an ingredient, not a replacement for those steps.
   Alternatively Laurent–Schrijver's complex-cone separation proof can be
   formalized, but that geometry is not currently an available theorem.
5. Apply the actual univariate lemma to each positive slice, obtain
   multivariate capacity descent, and handle the zero-capacity and
   vanished-polynomial cases without division by zero.
6. The finite telescoping product is completed in `CapacityMatrix.lean`.
   Identify the final mixed derivative coefficient with the existing Matrix.permanent.
   This yields the unconditional van der Waerden lower bound.
7. Formalize Laurent–Schrijver's matrix-specific first-derivative capacity
   bound with zero weights, then strict x log x convexity and column
   permutation. This yields the exact equality characterization.

Items 3–5 are still the substantial new formalization work. The univariate
lemma removes a real dependency, but it is not evidence that stability
closure or the van der Waerden theorem has already been proved in Lean.
