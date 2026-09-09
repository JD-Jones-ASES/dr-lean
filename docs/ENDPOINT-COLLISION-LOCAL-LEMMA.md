# Local lemma for the actual independent row law

[RowCollisionGraph](../DR/Endpoint/RowCollisionGraph.lean) and
[RowCollisionLocalLemma](../DR/Endpoint/RowCollisionLocalLemma.lean) specialize
the proved finite local lemma to actual independent row assignments.
Their accepted sources are Analytic-Lab P0174,
`ENDPOINT_RELATIVE_COLLISIONS.md`, section 1, and
`ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M.md`, section 3. The finite generic proof
and its literature attribution are described in
[ENDPOINT-LOCAL-LEMMA](ENDPOINT-LOCAL-LEMMA.md).

For nonnegative `X` with every row of total one, let `p_e` be the actual
probability that the two rows in the increasing pair `e` choose the same
column. Let `d_i` be the sum of incident edge probabilities, and let
`D = sum_e p_e`. The graph has exactly one edge per unordered pair. Its
neighbors share a row and exclude the edge itself. The formalization proves
the exact incident sum, `D` identity, and neighborhood-load bound
`sum_(f adjacent e) p_f <= d_i + d_h`. Joint nonneighbor independence follows
from the already proved row-coordinate product splitting.

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
refined bound includes `d=0`, and empty row sets are covered. There is no
new endpoint dimension range or blend-matrix conclusion in these modules.
The theorem can be applied separately to original and deleted row laws;
it does not identify those laws or their avoidance probabilities.

Verification: `lake build Test.RowCollisionLocalLemma` passed 1,945 jobs
with eight standard-only axiom audits and no warnings. Tests include an
actual 33-row model with a shared column of mass `1/16` and private columns
of mass `15/16`: every row load is exactly `1/8`, while `D=33/16>1`.
The proved local lemma supplies positive avoidance and all subset
conditional bounds for this model without enumerating its sample space.
Additional tests retain zero-probability edges and empty assignments, and
reject the refined scalar guard beyond its stated threshold.
