# Rectangular proof foundations

These modules advance the remaining rectangular targets. They do not replace
those targets with conditional inequalities or support-restricted statements.
The [theorem inventory](THEOREMS.md) still has four of twenty principal targets
proved. Every mathematical source below is in Analytic-Lab's P0174 evidence.

## Three rows at three samples

At an actual global maximum on a 3-by-N probability simplex, N>=3, every
physical column is now proved to be full or a doubleton: singleton and empty
columns are excluded. At least one full column exists. All three doubleton
types cannot occur simultaneously. The statements quantify over arbitrary
physical-column multiplicities, and support-preserving normalization retains
the original zeros and a positive lower floor on every occupied entry.

[ThreeRowFullColumn](../DR/Rectangular/ThreeRowFullColumn.lean) and
[ThreeRowThreeDoublets](../DR/Rectangular/ThreeRowThreeDoublets.lean) contain
these global statements. The two-star reduction used to exclude singleton
supports has actual normalized separation value N(N-1)/(N+1)^2. Its gap below
uniform is

    (N-2)(6N^2-7N-7) / [9N^2(N+1)^2] > 0,  N>=3.

The formula and its N=2 equality boundary are proved in
[ThreeRowTwoStar](../DR/Rectangular/ThreeRowTwoStar.lean).

For the remaining single-doubleton pattern, the scalar module
[ThreeRowSingleDoubletScalar](../DR/Rectangular/ThreeRowSingleDoubletScalar.lean)
excludes all positive blocks with S columns (0,b,b) and T columns (c,d,d),
where S,T>=1 and S+T>=3, from satisfying all four full-simplex first-order
conditions. This checkpoint contains that scalar exclusion; deriving every
condition from a normalized actual matrix is a separate bridge. The proof
uses both zero-entry derivative inequalities. Persistent tests show that
the positive-entry equations alone, N=2, and a zero full-block parameter
each permit configurations that the complete hypotheses exclude.

After that bridge, the two-doubleton-plus-full case is still required to
finish three rows. Four rows and the finite five-through-nine-row gaps also
remain before the complete K=3 release target can be claimed. Existing
unconditional infinite ranges are recorded in [the range map](ORDER-THREE-RANGES.md).
Sources: `SUPPORT_NORMAL_FORM.md`, `SINGLE_ZERO_RECTANGLE_K3.md`, and the
subsequent three-row support proofs.

## Four rows at four samples

The explicit polynomial two-column kernel is now identified with the actual
sampling kernel. For a nonnegative remaining-column board T, let s be its
total mass, alpha the sum of squared column masses, and V the squared
variance of its row marginals after division by s. The proved estimate is

    v^T C(T) v >= (13965659/8688000000) sum_i v_i^2

whenever s>=493/500, alpha<=7/2500 and V<=1/40. Zero cells and zero
columns are allowed. The reference kernel has floor 97/5792; the actual
column correction and its rank-one subtraction are retained.

[FourRowBlendBounds](../DR/Rectangular/FourRowBlendBounds.lean) proves the
estimate. [FourRowRook](../DR/Rectangular/FourRowRook.lean) proves the exact
kernel identification, and [FourRowAveraging](../DR/Rectangular/FourRowAveraging.lean)
turns it into a strict increase in the actual four-sample probability for
unequal columns and an interior blend. The factorial factor is 24. Thus
actual global maxima satisfying these explicit deletion bounds have equal
selected columns; the bounds themselves still have to be proved for every
contender in the intended range.

The remaining analytic inputs are the corrected leading minorant, scalar
gauge and contender concentration. Two finite quintic certificate families
cover the intermediate column counts; both remain pending. The complete
square N=4 case is already proved independently. The source is
`FOUR_ROW_K4_GLOBAL.md`, whose analytic cutoff N>=500 supersedes the earlier
N>=6400 cutoff. No conditional kernel estimate is counted as the complete
4-by-N theorem.

## Marginal concentration and row assignments

The canonical elementary sums now satisfy Newton and Maclaurin inequalities
on the closed nonnegative domain. For x>=0 of mass one on d coordinates, set

    E_k = d^k e_k(x) / choose(d,k),
    V = sum_i (x_i-1/d)^2.

For 2<=k<=d the formal proof gives

    E_k^2 <= [1-d V/(d-1)]^k,
    E_k >= 1-epsilon  ==>  V <= 2(d-1)epsilon/[d k(1-epsilon)],

with 0<=epsilon<1. Equality E_k=1 holds exactly at the uniform vector.
The [variance module](../DR/ElementarySymmetricBoundsVariance.lean) depends
on a multiplicity-aware real-rooted derivative argument, the exact reversed
polynomial-coefficient normalization, and a continuity argument that includes
zero coordinates. Tests retain repeated roots, evaluation at a root, sparse
vectors, binomial normalization and the nonunique order-one boundary.

[RowProduct](../DR/Endpoint/RowProduct.lean) independently samples one column
from each possibly different row law. Its avoidance probability is exactly
the endpoint rook sum of that row-stochastic matrix. For an original matrix
P with nonzero row masses,

    rookSum(P,m) = product_i rowSum(P,i) * rowAvoidance(normalizeRows(P)).

There is no factorial in this row-assignment formula. The separate iid-cell
intersection has an m! factor. Tests include unequal row masses, signed
weights, the empty assignment and zero-row normalization. Original row laws
and laws after deleting columns must be handled separately in later proofs.

Finally [FactorialDecay](../DR/Endpoint/FactorialDecay.lean) proves

    a_m = m!/m^m <= (1/2)^(m-1),  m>=1,
    a_m <= m^(-14),  m>=128.

Bernoulli proves the half-step recurrence; an exact base and rational ratio
bound prove the polynomial comparison for every later integer. This is the
concentration prerequisite from `ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`, not
a sampled factorial check or a completed endpoint range.

All modules use the standard Lean axiom allowlist. The full release still
requires the remaining principal proofs and the separate packaging and
independent verification gates in [VERIFICATION](VERIFICATION.md).
