# Linking participation masses to the localized collision estimates

`RowIncidenceLocalization.lean` proves that an actual single-doubleton
participation indicator equals the sum of its increasing-pair indicators.
The equality uses uniqueness of the actual nontrivial class and injectivity
of the increasing-pair representation. Taking the actual row expectation
gives an exact identity with `rowLocalizedDoubletonLoad`; division by zero
is retained by this algebraic identity.

`RowDeficitLocalization.lean` represents a tripleton containing row i by
the increasing pair of its other two rows. For two doubletons it chooses
the first class to contain i and the second to be disjoint. This proves
that actual deficit-two participation is at most the corresponding sum
of exact pattern indicators and masses. No independence is asserted here.
Its probability form explicitly assumes positive actual row avoidance.

`RowLocalizedExpectation.lean` combines these facts with the proved
expectation bound. The single-doubleton term is replaced by an exact
identity. The deficit-two term is replaced in the lower-bound direction,
because its coefficient is negative. The resulting quadratic form uses
exactly the localized loads already bounded in `RowCollisionLocalized`.

Replay: `lake build Test.RowIncidenceLocalization`. The interfaces retain
signed weights where only equalities are used, nonnegative unnormalized
weights for the mass bound, positive avoidance for the normalized matrix
bound, and empty row hosts. The deleted-board rook normalization remains
a separate obligation; this package does not claim a new endpoint range.
