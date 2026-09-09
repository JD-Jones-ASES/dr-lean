# Actual independent-row collision estimates

The endpoint transition proof in Analytic-Lab P0174
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`, section 2, uses one independent
column choice from each normalized row. These choices are independent but
need not have the same distribution. They are distinct from the original
iid cell samples that define `separationProbability`.

The new files derive this input from the existing `rowAssignmentEvent`
product law. Write X=normalizeRows(P), y_i=m*r_i, and

    p_ih = Pr(Z_i=Z_h), for i != h,
    d_i = sum_(h != i) p_ih,
    D = sum_(i<h) p_ih,
    W = sum_i (y_i-1)^2/y_i.

[RowCollisions](../DR/Endpoint/RowCollisions.lean) proves exact factorization
of coordinate constraints and the two-coordinate marginal identity. Thus
p_ih=sum_j X_ij X_hj for distinct rows. Its diagonal event is separately
proved to have mass one. These algebraic statements permit signed weights
provided every row sums to one; that hypothesis covers the unselected rows
too. No iid assertion or event-independence premise is inserted.

[RowCollisionUnion](../DR/Endpoint/RowCollisionUnion.lean) proves that D is
exactly half the ordered off-diagonal sum. Increasing pairs cover precisely
the complement of the injection event, yielding 1-rowAvoidance(X) <= D
for nonnegative normalized rows. This includes empty row assignments.

[RowCollisionBounds](../DR/Endpoint/RowCollisionBounds.lean) proves

    2D = sum_j (sum_i X_ij)^2 - sum_ij X_ij^2,
    d_i <= C/rmin,
    D <= (C/2) sum_i 1/r_i,
    sum_i 1/r_i = m^2+mW             when sum_i r_i=1.

Here colSum(P,j)<=C and 0<rmin<=r_i are literal marginal bounds. Weighted
Cauchy proves the total-mass estimate without replacing all reciprocal
rows by the rough smallest row. Zero entries and columns are allowed;
positive row sums are required before using their normalized probability
law. For actual endpoint contenders, that row positivity is derived by
the earlier contender theorem.

[RowCollisionContenders](../DR/Endpoint/RowCollisionContenders.lean) applies
the previously proved large-row column cap, obtaining for every actual
contender with m>=128 and n>=m:

    D <= (1/n+1/m^4)*m^2/2*(1+W/m),
    d_i <= 3m*(1/n+1/m^4)/(1-b),
    b = (n)_m/n^m.

The elementary avoidance lower bound refers specifically to the original
normalized-row law. Applying a generic estimate to a deleted board requires
its own retained-row positivity and normalization; no original contender
inequality is asserted for the deleted law.

The source owns the endpoint argument and constants; these Lean modules
prove its actual probability and normalization inputs. The sharper local
lemma avoidance estimate, transition-strip scalar comparisons, and final
endpoint maximizer closure are separate obligations. These modules alone
do not prove a new endpoint dimension range.

Replay with `lake build Test.RowCollisions`; the frozen replay passed 3,158
jobs and eleven standard-only axiom audits. The persistent controls include
signed row weights, diagonal-event exclusion, exactly three unordered edges
for three identical rows, an unnormalized zero row that invalidates the
marginal shortcut, unequal row-mass reciprocal correction, zero columns,
and the empty assignment. All final theorem audits use only Lean's standard
axioms.
