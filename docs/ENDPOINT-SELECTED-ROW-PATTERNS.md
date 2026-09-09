# Selected-row conditioning and removed collision edges

Three modules prove the probability comparison used for exact collision
patterns in Analytic-Lab P0174 `ENDPOINT_RELATIVE_COLLISIONS.md`, equations
(4) and (5):

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

Verification: `lake build Test.FinitePatternBound
Test.RowCollisionSelectedEvents` passed 2,191 jobs and nine standard-only
axiom audits with no warnings. A one-event test proves the restored
factor and refutes the inequality obtained by dropping it. An actual
two-row model gives positive prescribed-collision mass `1/16`, obtains
the `16/9` ratio bound after removing that edge, and verifies that keeping
the edge in avoidance instead gives mass zero. Further controls cover
internal-edge counting, both endpoints of the log chord, zero parameters,
and the empty selected set.

This establishes the general selected-event comparison. It does not yet
sum the explicit doubleton/tripleton patterns into the source's localized
collision penalties or conclude an endpoint maximizer range. Original
and deleted row laws remain separate inputs.
