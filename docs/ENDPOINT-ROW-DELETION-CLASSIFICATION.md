# Complete classification of two-row deletions

`DR/Endpoint/RowDeletionClassification.lean` proves the finite classification
needed by P0174 `ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`, Section 2. An actual
assignment whose column collisions disappear after deleting two distinct rows
is injective, has exactly one class of size two, has exactly one class of size
three, or has exactly two disjoint classes of size two. All remaining classes
are singletons. No distribution or optimizer is assumed.

The proof uses the actual column fibers of the deleted rows. Every other
fiber has at most one remaining row. If the deleted rows have the same column,
their fiber has size two or three. If they have different columns, both fibers
have size at most two; singleton classes are removed explicitly.

`rowDeletionMatrix_zero_or_pattern` gives the exhaustive form for arbitrary
assignments: the deletion matrix is zero or the assignment has one of these
four forms. It includes empty and one-row hosts and does not assert that a
zero matrix uniquely determines a collision pattern.

Replay: `lake build Test.RowDeletionClassification`. Tests include three
doubletons, a tripleton plus a doubleton, the genuine two-doubleton repair,
empty and singleton hosts, and the exact unrestricted theorem types. All
finite negative controls use ordinary kernel reduction. This module supplies
the classification only; averaging its quadratic bounds and connecting the
result to the actual deleted-board rook kernel are separate obligations.
