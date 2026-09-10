# Support of a minimum on the two-zero face

The four modules `TwoZeroCompetitor`, `PermanentSupportHall`,
`PermanentSupportBlocks`, and `TwoZeroFaceSupport` remove the zero-cofactor
alternative from the preceding face-stationarity prerequisite. They apply to
the actual doubly stochastic face with cells (0,1) and (1,0) forbidden, allowing
every additional zero. The matrix order is n+2 with n positive.

The explicit competitor adds a checkerboard of size 1/(n+2) to the leading
two-by-two block of the uniform matrix. Its permanent is exactly

    gamma(n+2) * (1 + 2/((n+2)(n+1))) < 2 gamma(n+2).

The calculation follows from a signed identity for any matrix with two
exceptional rows and all remaining rows constant. At order two the comparison
is equality, and the persistent tests retain this boundary.

A failure of strict Hall expansion for a doubly stochastic matrix supplies a
proper equal-cardinality support block. The actual block permanent bound and
`GammaBlockGap.dittertConstant_mul_ge_twice` give permanent at least twice the
uniform constant. Thus every minimum on the two-zero face has strict Hall
expansion. A fresh application of Hall's theorem constructs a full permutation
with any chosen row-column pair forced and every other matched cell positive.
Every cofactor is consequently positive, including cofactors at forbidden cells.
The one-sided comparison gives cofactor at least the permanent at
every allowed cell.

This is an internal proof of the support prerequisite. The [repeated-support reduction](TWO_ZERO_REDUCTION.md) uses these cofactor
bounds to derive the reduced matrix representation, which then yields the
[two-zero permanent gap](TWO_ZERO_PERMANENT.md). The application is motivated by
[Pula, Song and Wanless (2011)](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf).

Run `lake build +Test.TwoZeroFaceSupport` for the exact values, signed identity,
order-two boundary, failed strict Hall control, and full-face public statements.
