# Actual mixed quadratic coefficients and repeated-row permanents

This is a self-contained algebraic bridge for the two-zero-face averaging
route in Lab P0174 `TWO_ZERO_PERMANENT_GAP.md`. It reuses the previously proved
actual matrix-product polynomial, capacity reduction, and squarefree permanent
coefficient. It imports no external implementation.

For a signed `(n+2) x (n+2)` matrix A, form the product of its column linear
forms in row variables: `matrixProductPolynomial A.transpose`. Extract exponent
one in each of the first n variables using the actual `capacityReduce` operator.
The remaining variables label rows `Fin.natAdd n 0` and `Fin.natAdd n 1`.

The three coefficients are exactly:

- coefficient (2,0): permanent after repeating the penultimate row, divided by 2;
- coefficient (1,1): the original permanent;
- coefficient (0,2): permanent after repeating the final row, divided by 2.

All three identities allow arbitrary signed entries and n=0. Elimination
commutes with substitution in the surviving variables. Repeating row u into
row v is exactly the substitution `X_u -> X_u+X_v`, `X_v -> 0`. The coefficient
factor 2 is proved by expansion of a genuine homogeneous bivariate quadratic,
using Schrodinger's independently proved `homogeneous_fin_two_quadratic`.
No count, bijection, or matrix coefficient identity is assumed as an input.

Combining these identities with Schrodinger's self-contained actual stable
quadratic discriminant proves `permanent_repeated_rows_inequality` for every
entrywise nonnegative matrix, with zero rows/columns retained. It does not yet
assert existence of a two-zero face representative or prove support-preserving
averaging; those remain a separate matrix argument.

Owned production files: TwoZeroMixedDefinitions, TwoZeroMixedSubstitution,
TwoZeroMixedRepeat, TwoZeroMixedCoefficients. Schrodinger owns StableQuadratic
and TwoZeroMixedStability; neither is modified by this increment.

Replay: `lake build Test.TwoZeroMixedCoefficients`. Persistent tests check actual
signed 3x3 permanents and all coefficients, reject deleting the factor 1/2,
retain the empty eliminated prefix, check exponent-one restoration and actual
row substitution, include the zero matrix, and exhibit a signed matrix with
permanent 0 but both repeated-row permanents 2. Thus the algebraic identities
remain signed while the inequality's nonnegativity hypothesis is material.
