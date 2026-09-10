# Selected-row conditioning and removed collision edges

For an event determined by selected rows, the conditional local lemma
bounds its probability relative to full collision avoidance even when
specified collision edges are removed from the avoidance condition.
The proof has three parts:

* [FinitePatternBound](../DR/Endpoint/FinitePatternBound.lean) restores the
  local-lemma product for the forbidden edges removed from avoidance.
* [RowCollisionSelectedEvents](../DR/Endpoint/RowCollisionSelectedEvents.lean)
  supplies actual selected/complementary row independence and the finite
  touching-edge load bound.
* [RowCollisionTouchProduct](../DR/Endpoint/RowCollisionTouchProduct.lean)
  converts the touching-edge product into the explicit cardinality bound.

Let `V` be a selected finite row set, `A` an actual event on those row
coordinates, and `L` any set of collision edges touching `V`. Under
nonnegative normalized row laws and row collision loads at most `1/8`,
the final theorem states

```
Pr(A and avoid(all edges except L)) / rowAvoidance X
  <= (4/3)^|V| * Pr(A).
```

The actual probability of avoiding all edges is proved positive. The
numerator deliberately omits the prescribed internal edges `L` from its
avoidance family. The proof restores their complement product before
comparing with full avoidance. It never conditions a required collision
on avoidance of that same collision. The generic theorem does not assume
that `A` is a collision pattern; callers specifying a doubleton,
tripleton or two doubletons must supply their literal event and removed
edge set.

An edge touching two selected rows contributes once to the touching-edge
sum but twice to the sum of row loads. Thus `sum_touching 2*p_e <= |V|/4`.
Mathlib's concavity of the logarithm gives the closed chord inequality
`log(1-x) >= 4*x*log(3/4)` for `0 <= x <= 1/4`. Summing this inequality
proves the touching-edge product is at least `(3/4)^|V|`. The bound depends
on the number of selected rows, with no total collision intensity cap.

## Formal statements

[FinitePatternBound](../DR/Endpoint/FinitePatternBound.lean), [RowCollisionSelectedEvents](../DR/Endpoint/RowCollisionSelectedEvents.lean), [RowCollisionTouchProduct](../DR/Endpoint/RowCollisionTouchProduct.lean).
