# The proved infinite ranges at three samples

The sampling event is the inclusive OR of distinct rows and distinct
columns for three ordered iid cells. Every theorem here uses all
nonnegative real probability matrices, including zeros, and proves
both the sharp uniform bound and equality iff the matrix is uniform.
The all-rectangle K=3 release target remains pending.

After transposition, write m<=n. The compiled ranges are:

| Smaller side | Larger side | Declaration |
|---|---|---|
| 3 | n>=3 | `uniformMaximizer_three_rows` |
| 4 | n=4 | `uniformMaximizer_four_by_four_three` |
| 4 | n=5 | `uniformMaximizer_four_by_five_three` |
| 4 | n>=960 | `uniformMaximizer_orderThree_four_rows` |
| m>=10 | n>=m | `uniform_maximum_order_three_of_min_ge_ten` |
| 9 | n>=12 | `uniform_maximum_order_three_nine` |
| 8 | n>=15 | `uniform_maximum_order_three_eight` |
| 7 | n>=25 | `uniform_maximum_order_three_seven` |
| 6 | n>=238 | `uniform_maximum_order_three_six` |
| 5 | n>=121 | `uniform_maximum_order_three_five` |

The [complete three-row proof](THREE-ROW-PROOF.md) includes all N>=3 and
its transpose. The 3-by-3 endpoint is also proved independently in the square
package. The remaining rectangles are finite: 4-by-4, 4-by-5, and the
1,330 stored certificate cases (4-by-6 through 4-by-959 and the remaining
five-through-nine-row ranges). A criterion failing outside the table is
not a counterexample to P2.

## Actual probability and energy bounds

[OrderThreeSampling](../DR/Rectangular/OrderThreeSampling.lean) proves
that simultaneous row and column failure has the literal cubic polynomial
in [OrderThreePolynomial](../DR/Rectangular/OrderThreePolynomial.lean).
The identity is homogeneous and holds even for signed weights. Its
probability specialization uses nonnegative mass-one matrices.

[OrderThreeLargeExpansion](../DR/Rectangular/OrderThreeLargeExpansion.lean)
expands the failure gap about uniform. The centered matrix splits exactly
into row, column and zero-marginal parts. The mixed cubic term is bounded
by finite Cauchy-Schwarz, retaining zero projection energies. The
[far bound](../DR/Rectangular/OrderThreeLargeFar.lean) is strict when the
squared centered norm is at least 2/(mn). The
[near bound](../DR/Rectangular/OrderThreeLargeNear.lean) multiplies that
norm by an explicit rational dimension criterion. Its
[dimension proof](../DR/Rectangular/OrderThreeLargeDimensions.lean)
establishes the general large-board and six-through-nine-row ranges without sampling dimensions.
[OrderThreeLarge](../DR/Rectangular/OrderThreeLarge.lean) gives the final
probability inequalities, exact equality case and transposition wrappers.

## Five rows

The five-row refinement keeps the row and column energies separately,
uses the stronger zero-sum row-coordinate bound, and completes the column
square before the final normalization. It never divides by either
marginal energy. The
[scalar estimate](../DR/Rectangular/OrderThreeLargeFiveScalar.lean) and
[normalization](../DR/Rectangular/OrderThreeLargeFiveNormalize.lean)
give the exact positive near-region margin 27197/2772275 for every n>=121.
The [final theorem](../DR/Rectangular/OrderThreeLargeFive.lean) combines
that estimate with the same far-region result and includes both orientations.

Persistent tests cover zero and pure marginal deviations, a pure
interaction direction, the sharp mixed-term control, a rejected stronger
row-coordinate bound, threshold values, transposition and matrices with
zero entries. See [the general tests](../Test/OrderThreeLarge.lean) and
[the five-row tests](../Test/OrderThreeLargeFive.lean).

## Four rows

The complete N>=960 strip is proved in
[OrderThreeFourRowFinal](../DR/Rectangular/OrderThreeFourRowFinal.lean), including
the transposed family. The [leading gauge account](FOUR-ROW-INPUTS.md) gives
the exact scalar and copositive inequalities. Their actual contender bootstrap
proves gauge variance times N^2<5, row variance times N<14, each column
mass<7/N, and row variance<1/64.

The first-order residual averaging kernel then has a 1/8 quadratic floor
on every real vector after any two distinct columns are removed. Exact
sampling gives a midpoint gain at least 3/16 times the squared difference
of those columns. Hence global maximizers have equal columns; positive
row masses and the proved positive-matrix K=3 uniqueness theorem finish
the result. Every concentration and support statement is derived internally.

The mathematical sources are Analytic-Lab's P0174 `LARGE_RECTANGLES.md` and `FOUR_ROW_STRIP.md`;
the formal proof keeps its constants and full boundary scope. This range
map concerns compiled partial families, not the entire twenty-target release.
