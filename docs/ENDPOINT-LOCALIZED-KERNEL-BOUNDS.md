# Localized collision bounds from the actual normalized column cap

`DR/Endpoint/RowCollisionKernelBounds.lean` connects the proved relative
pattern estimates to three scalar fields of `EndpointCollisionKernelBounds`.
For nonnegative normalized rows and a column cap `C>=0`, the single exact
condition `m*C^2<=1/256` yields positive no-collision probability, mean
single-pair load at most `1/4`, centered squared single-pair load at most
`1/64`, and every localized deficit-two load at most `1/4`.

This is Section 3 of the Lab's `ENDPOINT_LLL_STRIP.md` with square roots
eliminated from the final arithmetic. Increasing pairs and the actual
original normalized row law are inherited from the proved pattern
lemmas. Centering decreases the squared norm. No upper bound on total
collision intensity is assumed, and division by the actual avoidance
probability is justified by the finite local lemma.

Replay: `lake build Test.RowCollisionKernelBounds`. The tests instantiate
three uniform rows on 128 columns and preserve arbitrary zero-cell laws
in the semantic theorem signature. The dimension factor in the cap has
an explicit failed-omission control. This supplies local scalar inputs;
retained-row balance and the elementary coefficient remain separate.
