# Rectangular proof foundations

The rectangular proofs use collision identities, marginal concentration,
and averaging on the full probability simplex. The intermediate estimates
below are connected to the original sampling probability in the linked
proofs. [Theorems](THEOREMS.md) lists their exact conclusions.

## Two samples

At two samples, failure means drawing the same cell twice. Therefore

    F_2(P) = 1 - sum_ij P_ij^2,
    F_2(U) - F_2(P) = sum_ij (P_ij - 1/(mn))^2.

Every term on the right is nonnegative, and the sum vanishes exactly at
uniform. [OrderTwo](../DR/Rectangular/OrderTwo.lean) proves this identity
and the sharp theorem for all nonempty rectangles, including zero entries.

## Every order on sufficiently large rectangles

For k>=4, write c=choose(k,2)*choose(choose(k,2)^2,2) and
D_k=128(k-2)(c+1)^2. If both dimensions are at least D_k, the uniform board
is the unique maximizer. [LargeBoards](../DR/Rectangular/LargeBoards.lean)
also proves the simpler sufficient threshold min(m,n)>=k^21.

To prove this, choose a global maximizer by compactness. Since it does at
least as well as uniform, collision estimates bound its marginal deviations.
After any two columns are removed, the retained matrix has positive mass;
its normalization satisfies the concentration hypotheses of the occupation
kernel bound. If C is the averaging kernel and E its positive coefficient,
then for every real row vector x,

    x^T C x >= (2/5) E sum_i x_i^2.

Averaging two columns changes the objective by a positive multiple of this
quadratic form at their difference. At a maximum the increase is at most
zero, so the columns must agree. Applying the same argument after
transposition forces equal rows. Total mass one then identifies the matrix
as uniform. This classifies every maximizer and gives both the sharp bound
and its exact equality case on the full closed simplex. The argument uses
no square Dittert theorem or permanent lower bound.

## Three rows at three samples

The complete sharp inequality and exact equality case hold on every
3-by-N probability simplex, N>=3, and its transpose. The
[three-row proof](THREE-ROW-PROOF.md) explains the support-preserving reduction
and exclusion of every one-, two-, and three-doubleton boundary family.
[ThreeRowFinal](../DR/Rectangular/ThreeRowFinal.lean) is the final integration
entry. All original zero entries are covered. The N=2 countercontrol proves
that the lower dimension guard is necessary for uniqueness.

The four-row K=3 strip N>=960 is also proved, including its transpose.
The finite four-through-nine-row cases and all infinite ranges are joined
in the [complete K=3 proof](ORDER-THREE-COMPLETE.md).

## Four rows at four samples

The explicit polynomial two-column kernel is identified with the actual
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
selected columns. The actual contender bounds are supplied by the analytic
tail argument described below.

The scalar gauge bound is proved independently in
[FourRowScalarGauge](../DR/Rectangular/FourRowScalarGauge.lean):

    (sum_i r_i sqrt(1-g_i))^2 >= 29/32 + (61/512) sum_i(r_i-1/4)^2.

Equality at 29/32 is equivalent to uniform rows. A degree-seven symmetric
polynomial is moved to sorted gap coordinates; the exact quantitative
residual has 115 positive integer coefficients after scaling by 1024. Lean
proves its literal identity, permutation invariance, nonnegativity, and the
boundary-safe square-root step. The generator reproduces this certificate
from the source formula. The tests retain zero mass and the sharp polynomial
constant at a simplex vertex.

The actual initial contender cap is unconditional, and the complete sharper
concentration and pair-deletion normalization argument is proved from the
three leading inputs in
[FourRowContenderConcentration](../DR/Rectangular/FourRowContenderConcentration.lean).
The scalar input and actual collision remainder are discharged. The
[four-row input account](FOUR-ROW-INPUTS.md) gives the exact remainder and
the complete corrected minorant and its actual compact-extremum reductions.
The full closed-simplex K=4 analytic tail N>=500 and its transpose are proved
in [FourRowTail](../DR/Rectangular/FourRowTail.lean). Two finite quintic certificate
families cover the intermediate column counts in the
[complete four-row theorem](FOUR-ROW-PROOF.md). The square N=4 case is proved
independently. These three ranges cover every N>=4.

## Marginal concentration and row assignments

The canonical elementary sums satisfy Newton and Maclaurin inequalities
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

The [endpoint contender bridge](../DR/Endpoint/Contenders.lean) proves,
for a=m!/m^m, b=(N)_m/N^m, normalized row product R, normalized column
success S, and normalized rook value T,

    F_m(P)=a R+b S-a T,
    (1-R)+(b/a)(1-S) <= b-T,
    1-b <= R(1-p_original).

Every contender has positive original row sums before its probability law
is normalized. Its original avoidance obeys 0<=p_original<=b<1. Exact
row and column variance bounds follow from Maclaurin. The remaining factor
1-p_original is retained in the row-product deficit bound. For m>=128,
[LargeRowCaps](../DR/Endpoint/LargeRowCaps.lean) proves the actual contender
column cap c_j<1/N+1/m^4. The
[deleted-law module](../DR/Endpoint/DeletedLaw.lean) uses its own retained
row masses; positive retained total mass alone does not justify treating
all retained rows as probability laws.

Finally [FactorialDecay](../DR/Endpoint/FactorialDecay.lean) proves

    a_m = m!/m^m <= (1/2)^(m-1),  m>=1,
    a_m <= m^(-14),  m>=128.

Bernoulli proves the half-step recurrence; an exact base and rational ratio
bound prove the polynomial comparison for every later integer. This concentration estimate is used in the
[all-aspect endpoint proof](ENDPOINT-ALL-ASPECTS.md).

The proof dependencies are checked by the full transitive axiom audit.
[Verification](VERIFICATION.md) gives the reproducible commands.
