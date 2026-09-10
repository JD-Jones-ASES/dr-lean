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

The [participation identities](ENDPOINT-PARTICIPATION-LOCALIZATION.md)
express u_i exactly as the sum of the doubleton masses involving i,
and bound v_i by the corresponding deficit-two pattern sum.
[Deleted-row rook normalization](ENDPOINT-ROW-DELETION-ROOK.md)
then converts this expectation into the endpoint averaging kernel.

## Formal statements

[RowCollisionIncidence](../DR/Endpoint/RowCollisionIncidence.lean), [RowDeletionExpectation](../DR/Endpoint/RowDeletionExpectation.lean).
