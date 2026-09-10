# Stable quadratic prerequisite for permanent averaging

`StableQuadratic` expands every homogeneous polynomial of degree two in two
variables into its three actual monomial coefficients. A positive slice of an
H-stable homogeneous polynomial splits over the reals by the already proved
`StableSlices` theorem. A real quadratic with a root has nonnegative
discriminant; a zero leading coefficient is handled separately. This proves
4 c20 c02 <= c11^2, including the zero polynomial. Nonnegative coefficients
are not needed in this final two-variable argument.

`TwoZeroMixedStability` applies the actual derivative and zero-specialization
closure at every step of `permanentQuadraticReduce`. A nonnegative matrix's
row-product polynomial either has a zero factor or is H-stable. Thus arbitrary
zero rows and columns are retained throughout the reduction. The mixed
coefficient is the actual permanent, giving 4 c20 c02 <= permanent(A)^2.

The independent `TwoZeroMixedCoefficients` algebra identifies the two pure
coefficients with one half of the corresponding repeated-row permanents.
That identification turns this discriminant bound into the classical
Alexandrov permanent inequality. [Face averaging](TWO_ZERO_REDUCTION.md) and the
[two-zero floor](TWO_ZERO_PERMANENT.md) follow from this inequality.

The stability closure used here was formalized from
[Gurvits (2008)](https://arxiv.org/abs/0711.3496v2).
For the classical permanent inequality and its averaging context, see
[van Lint's survey](https://pure.tue.nl/ws/files/4254844/696880.pdf).

Run `lake build +Test.StableQuadratic +Test.TwoZeroMixedStability`.
The tests include zero polynomials, missing leading terms, a forbidden
negative-discriminant stable quadratic, a repeated root, signed homogeneous
expansion, a zero row, and the actual matrix permanent normalization.
