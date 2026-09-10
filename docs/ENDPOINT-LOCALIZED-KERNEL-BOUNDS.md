# Localized collision bounds from the actual normalized column cap

`DR/Endpoint/RowCollisionKernelBounds.lean` connects the proved relative
pattern estimates to three scalar fields of `EndpointCollisionKernelBounds`.
For m≥1 nonnegative normalized rows and a column cap `C>=0`, the single exact
condition `m*C^2<=1/256` yields positive no-collision probability, mean
single-pair load at most `1/4`, centered squared single-pair load at most
`1/64`, and every localized deficit-two load at most `1/4`.

Increasing pairs represent each unordered collision once. The exact
pattern ratios bound the uncentered localized loads, and subtracting
their mean decreases the squared norm. The finite local lemma proves
positive avoidance before the normalized loads are divided by it.
No upper bound on total collision intensity is needed.

## Formal statements

[RowCollisionKernelBounds](../DR/Endpoint/RowCollisionKernelBounds.lean).
