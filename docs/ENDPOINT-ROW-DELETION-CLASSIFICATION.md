# Complete classification of two-row deletions

An assignment whose column collisions disappear after deleting two
distinct rows is injective, has exactly one class of size two, has exactly
one class of size three, or has exactly two disjoint classes of size two.
All other classes are singletons. This classification is pointwise and
requires no probability distribution.

The proof uses the actual column fibers of the deleted rows. Every other
fiber has at most one remaining row. If the deleted rows have the same column,
their fiber has size two or three. If they have different columns, both fibers
have size at most two; singleton classes are removed explicitly.

`rowDeletionMatrix_zero_or_pattern` gives the exhaustive form for arbitrary
assignments: the deletion matrix is zero or the assignment has one of these
four forms. It includes empty and one-row hosts and does not assert that a
zero matrix uniquely determines a collision pattern.

## Formal statements

[RowDeletionClassification](../DR/Endpoint/RowDeletionClassification.lean).
