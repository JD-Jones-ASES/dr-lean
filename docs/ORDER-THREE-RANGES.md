# The proved infinite ranges at three samples

The sampling event is the inclusive OR of distinct rows and distinct
columns for three ordered iid cells. Every theorem here uses all
nonnegative real probability matrices, including zeros, and proves
both the sharp uniform bound and equality iff the matrix is uniform.
The all-rectangle K=3 release target remains pending.

After transposition, write m<=n. The compiled ranges are:

| Smaller side | Larger side | Declaration |
|---|---|---|
| m>=10 | n>=m | `uniform_maximum_order_three_of_min_ge_ten` |
| 9 | n>=12 | `uniform_maximum_order_three_nine` |
| 8 | n>=15 | `uniform_maximum_order_three_eight` |
| 7 | n>=25 | `uniform_maximum_order_three_seven` |
| 6 | n>=238 | `uniform_maximum_order_three_six` |
| 5 | n>=121 | `uniform_maximum_order_three_five` |

The complete 3-by-3 endpoint is proved separately in the square package.
The three-row family, four-row family and remaining finite rectangles
are still work in progress. A criterion failing outside the table is
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
establishes the first five rows of the table without sampling dimensions.
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

The mathematical source is Analytic-Lab's P0174 `LARGE_RECTANGLES.md`;
the formal proof keeps its constants and full boundary scope. This range
map concerns compiled partial families, not the entire twenty-target release.
