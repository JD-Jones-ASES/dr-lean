# Finite conditional local lemma and actual row laws

For finitely many events under a probability law, neighborhood-product
bounds and independence from joint nonneighbor avoidance imply positive
probability of avoiding every event. The conditional form also controls
an additional event depending on a specified set of coordinates.

The conditional local-lemma framework is due to Haeupler, Saha and
Srinivasan, [New Constructive Aspects of the Lovasz Local Lemma](https://arxiv.org/abs/1001.1231v5),
Theorems 1.1 and 2.1. The finite argument here derives the conditional
product bound from finite weighted sums and independence of disjoint
row coordinates.

For a finite sample space with nonnegative weights of total one, the
formal theorem derives positive avoidance and the conditional bound
`Pr(E_e and avoid S) <= x_e Pr(avoid S)`, assuming `0 <= x_e < 1`, the
asymmetric neighborhood-product inequality, and independence from joint
avoidance of every nonneighbor family. Positivity is a conclusion. Zero
events and zero parameters are retained. Graph symmetry is unnecessary
for the generic theorem. Pairwise independence alone is not a premise
that suffices.

The product lower bound and arbitrary-event extension are separate
corollaries. The latter keeps all denominators cleared:

```
Pr(F and avoid S) * product_(e in S intersect NF) (1-x_e)
  <= Pr(F) * Pr(avoid S).
```

The independence premise for an actual independent row law is supplied
by [RowAssignmentIndependence](../DR/Endpoint/RowAssignmentIndependence.lean).
Its selected/complementary coordinate splitting and observable identities
hold even for signed row weights. Under row normalization, an actual row
collision is independent of joint avoidance of collision pairs whose
endpoints are disjoint from its two rows. Shared-row independence is
neither assumed nor asserted.

## Formal statements

[FiniteAvoidance](../DR/Endpoint/FiniteAvoidance.lean), [FiniteLocalLemma](../DR/Endpoint/FiniteLocalLemma.lean), [RowAssignmentIndependence](../DR/Endpoint/RowAssignmentIndependence.lean).
