# Local lemma for the actual independent row law

The collision graph specializes the [finite conditional local lemma](ENDPOINT-LOCAL-LEMMA.md)
to independent, possibly nonidentically distributed column choices, one
from each row. Its local hypotheses control incident collision probabilities
rather than their total sum.

For nonnegative `X` with every row of total one, let `p_e` be the actual
probability that the two rows in the increasing pair `e` choose the same
column. Let `d_i` be the sum of incident edge probabilities, and let
`D = sum_e p_e`. The graph has exactly one edge per unordered pair. Its
neighbors share a row and exclude the edge itself. The finite conditional argument proves
the exact incident sum, `D` identity, and neighborhood-load bound
`sum_(f adjacent e) p_f <= d_i + d_h`. Joint nonneighbor independence follows
from the proved row-coordinate product splitting.

The reusable scaled theorem takes a scalar bound `d_i <= d` and a
nonnegative parameter `c` satisfying

```
c*d < 1,          1 <= c*(1-2*c*d).
```

It derives the asymmetric local-lemma condition for `x_e=c*p_e`. Every
avoidance family then has positive actual probability, each remaining edge
satisfies the conditional bound, and the corresponding complement product
is a lower bound on actual avoidance. No event-independence assertion or
positive avoidance conclusion appears as an unproved premise.

Two explicit consequences are proved:

* If every `d_i <= 1/8`, use `c=2`. In particular `rowAvoidance X > 0`.
* If `0 <= d <= 1/8`, use `c=1/(1-4*d)`. This gives the sharper product
  `product_e (1-p_e/(1-4*d)) <= rowAvoidance X` used in the transition proof.

Neither result assumes that `D` is small. Zero edges are retained, the
refined bound includes `d=0`, and empty row sets are covered.
The theorem can be applied separately to original and deleted row laws;
it does not identify those laws or their avoidance probabilities.

## Formal statements

[RowCollisionGraph](../DR/Endpoint/RowCollisionGraph.lean), [RowCollisionLocalLemma](../DR/Endpoint/RowCollisionLocalLemma.lean).
