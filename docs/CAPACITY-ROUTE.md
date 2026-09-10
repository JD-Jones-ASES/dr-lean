# Capacity route for the full square permanent prerequisite

The van der Waerden inequality and its full equality characterization are
proved in
`DR/Square/CapacityEquality.lean`, including dimensions zero and one.
`vanDerWaerden_with_equality` assumes only that the input matrix is doubly
stochastic. These prerequisites feed the all-order square Dittert
theorem listed in [THEOREMS](THEOREMS.md).

The proof proceeds through an explicit split-polynomial bridge, actual
complex half-plane stability, positive slices, closure under differentiation
and specialization, capacity descent, the permanent coefficient identity,
and the exact matrix equality case. All these dependencies are internal
proved lemmas; the module map appears below.

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
The zero-capacity, vanished-derivative, and empty-product cases are covered
in [Test.Stability](../Test/Stability.lean).

## Univariate and matrix capacity lemmas

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

[CapacityPolynomial.lean](../DR/Square/CapacityPolynomial.lean) converts a
split real polynomial to the finite affine-factor representation, including
nonpositive roots, multiplicities, degree padding, and the zero polynomial.

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

Half-plane stability, its differentiation and specialization rules, and
the permanent inequality with equality are proved in the modules below.
They build on the listed polynomial and convexity results from Mathlib.

## Dependency map

1. `CapacityMatrix.lean` gives the initial capacity normalization and finite
   telescoping product.
2. `CapacityPolynomial.lean` gives the actual root/factorization bridge,
   including degree padding and zero cases.
3. `CapacityStability.lean` defines homogeneous half-plane nonvanishing and
   proves the nonnegative matrix polynomial satisfies it with capacity one.
4. `StableSlices.lean` and `NormComparison.lean` prove positive-slice splitting
   and Gurvits's norm comparison. `StableClosure.lean` and
   `StableDerivative.lean` prove coefficient limits, positive directional
   derivatives, coordinate derivatives and zero specialization, retaining
   the zero-polynomial alternative.
5. `CapacityDescent.lean` and `CapacityBound.lean` apply the actual univariate
   lemma to each positive slice and iterate the capacity inequality. They
   handle zero capacity without dividing by it.
6. `PermanentCoefficient.lean` identifies the final squarefree coefficient
   with `Matrix.permanent`, yielding the unconditional lower bound.
7. `CapacityEqualityDeletion.lean`, `CapacityEqualityEntropy.lean` and
   `CapacityEquality.lean` prove the first-deletion entropy bound, strict
   closed-simplex equality, and the column-permutation argument. The final
   `vanDerWaerden_with_equality` covers every doubly stochastic matrix.

[Verification](VERIFICATION.md) gives the build and transitive axiom checks.
[Capacity equality tests](../Test/CapacityEquality.lean) retain unit column
entries, zero weights and exact uniform attainment.
