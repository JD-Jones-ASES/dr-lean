# Literal row-deletion matrices for exact collision patterns

[RowDeletionPatterns](../DR/Endpoint/RowDeletionPatterns.lean) defines the
actual zero-diagonal matrix `L(z)`: for distinct rows `a,b`, its entry is
one exactly when deleting those two rows leaves distinct sampled columns.
It is symmetric, and its diagonal is explicitly zero.

For the exact one-class and two-class events already used in the
probability bounds, the module proves the complete row-equality relation.
After deleting any row set `S`, distinctness is therefore equivalent to
each prescribed class retaining at most one member. This derives the
source's pointwise matrix forms in P0174
`ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`, section 1:

* With no collisions, `L = J-I`.
* For one doubleton with incidence vector `e`,
  `-L = diag(e)-1 e^T-e 1^T+e e^T` entry by entry.
* For a tripleton, `L` is exactly `K3` on its three rows.
* For two disjoint doubletons, `L` is exactly `K2,2` between the classes.
* A single class of size at least four cannot be repaired by deleting
  two rows, so its deletion matrix is zero.

These are dimension-independent conditional statements whose hypotheses
are literal sample-pattern events. They do not assume the desired matrix
inequality. Classification of every assignment admitting a successful
two-row deletion, the full higher-deficit exclusion, and the expectation
comparison remain separate obligations. The rook normalization and
endpoint parameter-range proof also remain unfinished.

Verification: `lake build Test.RowDeletionPatterns` passed 2,193 jobs,
with nine standard-only axiom audits and no warnings. Exact finite sample
assignments exercise all four collision patterns, successful and failed
deletions, the zero diagonal, and exclusion of within-class edges from
the two-doubleton `K2,2`. A negative control shows that dropping the
positive incidence rank-one term changes the exact doubleton identity.

The independent square-completion target is recorded separately in
[ENDPOINT-MATRIX-INTERFACE](ENDPOINT-MATRIX-INTERFACE.md), explicitly as
an unproved proposed interface for a later available work slot.
