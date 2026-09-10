# Literal row-deletion matrices for exact collision patterns

[RowDeletionPatterns](../DR/Endpoint/RowDeletionPatterns.lean) defines the
actual zero-diagonal matrix `L(z)`: for distinct rows `a,b`, its entry is
one exactly when deleting those two rows leaves distinct sampled columns.
It is symmetric, and its diagonal is explicitly zero.

For an exact one-class or two-class collision event, deleting a row set S
leaves distinct columns precisely when each prescribed class retains at
most one member. Consequently the pointwise deletion matrices are:

* With no collisions, `L = J-I`.
* For one doubleton with incidence vector `e`,
  `-L = diag(e)-1 e^T-e 1^T+e e^T` entry by entry.
* For a tripleton, `L` is exactly `K3` on its three rows.
* For two disjoint doubletons, `L` is exactly `K2,2` between the classes.
* A single class of size at least four cannot be repaired by deleting
  two rows, so its deletion matrix is zero.

The [exhaustive classification](ENDPOINT-ROW-DELETION-CLASSIFICATION.md)
shows that these cases cover every nonzero deletion matrix. The
[quadratic estimates](ENDPOINT-ROW-DELETION-QUADRATIC.md) and
[expectation identity](ENDPOINT-ROW-DELETION-EXPECTATION.md) therefore
apply to every assignment, without a support restriction on the input law.

The [matrix completion](ENDPOINT-MATRIX-INTERFACE.md) bounds the
resulting averaged form after its collision loads have been estimated.

## Formal statements

[RowDeletionPatterns](../DR/Endpoint/RowDeletionPatterns.lean).
