# Actual collision participation and the expectation bound

`RowCollisionIncidence.lean` defines whether an actual assignment has
exactly one doubleton or collision deficit two, and whether a specified
row participates in a collision. Combining these gives zero-one row
incidence functions. A tripleton row contributes one, even though it has
two collision partners. The two-doubleton definition is independent of
the order of the two class names.

The complete `rowDeletion_pointwise_lower` theorem follows from the
exhaustive two-row deletion classification and the proved quadratic
bounds. It contains no assumed optimizer shape or probability bound.

`RowDeletionExpectation.lean` averages this theorem with the actual row
assignment mass. It proves, for every real vector x,

```
-q(E[L], x) ≥ p0 (sum x_i² - (sum x_i)²)
             + sum u_i x_i² - 2 (sum x_i)(sum u_i x_i)
             - 2 sum v_i x_i².
```

Here p0 is the actual row-avoidance mass; u and v are the actual
participation masses just defined. Nonnegative board entries suffice.
Row normalization is unnecessary for the theorem, so its scope also
includes zero rows and unnormalized nonnegative weights. The interchange
and indicator equalities themselves allow signed weights.

This is P0174 `ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`, equation (3), in
explicit quadratic form. The earlier localized probability estimates
use sums indexed by increasing sample pairs. Identifying the single-pair
participation mass with that sum and bounding the deficit-two mass by
its corresponding sum remain explicit next obligations, as does the
deleted-board rook normalization.

Replay: `lake build Test.RowCollisionIncidence Test.RowDeletionExpectation`.
Controls distinguish participants from edge counts and use a nonnormalized
three-row law of total assignment mass thirty. Empty rows, signed equality
interfaces, and the zero diagonal are retained.
