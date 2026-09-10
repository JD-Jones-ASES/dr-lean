# The complete three-row K=3 theorem

For every integer N>=3 and every nonnegative 3-by-N matrix P of total mass
one, the probability that three independent cells have distinct rows or
distinct columns is at most

    1 - 7/(3N) + 14/(9N^2),

with equality exactly at the uniform matrix. The OR is inclusive. The
transpose has the same conclusion on N-by-3 boards. The final declarations
are `uniformMaximizer_three_rows` and `uniformMaximizer_three_columns` in
[ThreeRowFinal](../DR/Rectangular/ThreeRowFinal.lean).

The proof works on the entire closed probability simplex. Positivity and
support regularity are conclusions about a maximizer, not hypotheses of
the theorem. N=2 cannot be included in the uniqueness assertion: the board
whose first column is (1/3,1/3,1/3) and second column is zero already attains
the uniform value 2/9. [The final tests](../Test/ThreeRowFinal.lean) prove this
countercontrol as well as the arbitrary-N statement and its transpose.

## Reduction to supports

Compactness provides a global maximum. Full-simplex derivative conditions
apply at both positive entries and zeros. Averaging rows or columns with
the same actual support preserves the maximum. A minimum-norm representative
among maximizers with an occupied-entry lower floor therefore has equal
rows and columns within each support class. Every original zero and every
original positive entry is retained by this normalization.

The earlier [positive-maximizer theorem](../DR/Rectangular/ThreeRowPositive.lean)
shows that an original positive global maximizer is uniform, using exact
cubic interpolation and strict local uniqueness. It remains to eliminate
all supports containing a zero. Empty axes are excluded first. The singleton
argument reduces to an actual two-star matrix and compares its exact value
with uniform. Thus every physical column is full or has exactly one missing
row. A board with only doubletons is excluded too, so at least one full
column exists. These conclusions hold for arbitrary column multiplicities.

There are only three possible doubleton types, indexed by their missing row.
The final argument excludes each possible nonzero number of occurring types.

## One, two and three doubleton types

With one type, support-preserving row and column normalization gives S
columns (0,b,b) and T columns (c,d,d), up to row positions, with S,T>=1,
S+T>=3 and b,c,d>0. The
[actual block bridge](../DR/Rectangular/ThreeRowSingleDoubletBoard.lean)
derives four first-order conditions, including both zero-entry inequalities.
The [scalar exclusion](../DR/Rectangular/ThreeRowSingleDoubletScalar.lean)
contradicts them using residual-mass ratios and exact integer size borders.
The [normalization wrapper](../DR/Rectangular/ThreeRowSingleDoubletNormal.lean)
therefore excludes the original arbitrary maximizer on this support.

With two types, their omitted-row masses are unequal. After ordering them,
the full-column derivative conditions give a strict residual majority and
an offset relation. A sum over every remaining physical column forces an
exclusive entry to exceed its common-row entry. Comparing that doubleton
with a full column then yields two linear equations and a missing-row
inequality. The [scalar inverse obstruction](../DR/Rectangular/ThreeRowTwoDoubletScalar.lean)
contradicts these equations without dividing by a determinant. All three
residual row masses are proved positive from an actual remaining column.
[ThreeRowTwoDoublets](../DR/Rectangular/ThreeRowTwoDoublets.lean) and its
[normalization wrapper](../DR/Rectangular/ThreeRowTwoDoubletNormal.lean)
retain every physical column and every support boundary.

With all three types, the omitted-row masses are pairwise unequal. Two
strict residual majorities contradict the ordered full-column offsets.
[ThreeRowThreeDoublets](../DR/Rectangular/ThreeRowThreeDoublets.lean) transfers
that contradiction through support-preserving normalization. This exhausts
every zero-support possibility. The original maximizer is consequently
positive and hence uniform. Compactness gives the sharp inequality for all
P; any matrix attaining the same value is itself a maximizer, proving the
exact equality statement. A zero entry in P therefore gives strict loss.

## Relation to the full three-sample theorem

This proves an infinite rectangular family by exact support and derivative
arguments. [The range map](ORDER-THREE-RANGES.md) explains the remaining
infinite estimates, and [the complete assembly](ORDER-THREE-COMPLETE.md)
joins them with finite certificates to cover every admissible rectangle.
