# Exact normalization of deleted-row rook sums

`DR/Endpoint/RowDeletionRook.lean` connects the actual rook sum on a board
with erased rows to an event of its independent normalized row law.
For a deleted row set S and k remaining rows it proves

```
rookSum(eraseRows(P,S), k)
  = (product of remaining row masses)
    * Pr[columns are distinct outside S under normalizeRows(P)].
```

The rook sum has no factorial. Its definition sums over increasing row
embeddings, and only the increasing embedding of the remaining row set
can contribute. Every other term contains an erased row and is zero.
The actual event identity integrates unused rows using their normalized
product law, then reindexes the remaining rows by their order isomorphism.

The exact identity permits signed row weights when each row mass is
nonzero. The event theorem separately requires normalized rows. Neither
the final desired endpoint inequality nor positivity of a blend kernel
is assumed. Applying this theorem to a board obtained by deleting columns
uses that board's own row normalization. It does not substitute the
original-board collision-avoidance probability.

## Formal statements

[RowDeletionRook](../DR/Endpoint/RowDeletionRook.lean).
