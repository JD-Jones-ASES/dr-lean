# Finite conditional local lemma and actual row laws

The finite probability input to the endpoint collision argument is proved in
[FiniteAvoidance](../DR/Endpoint/FiniteAvoidance.lean) and
[FiniteLocalLemma](../DR/Endpoint/FiniteLocalLemma.lean). The source is the
finite induction spelled out in Analytic-Lab P0174,
`ENDPOINT_RELATIVE_COLLISIONS.md`, section 1. That note attributes the
asymmetric local lemma and its conditional-distribution extension to
Haeupler, Saha and Srinivasan, *New Constructive Aspects of the Lovasz Local
Lemma*, arXiv:1001.1231v5, Theorems 1.1 and 2.1.

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

The generic local lemma does not yet assert an endpoint range, a relative
exact-pattern estimate, or a positive blend matrix. The collision-graph
specialization must still establish its neighborhood-product hypothesis.
For exact patterns, internal prescribed collision edges must be removed
from the avoidance family and then accounted for separately. Original and
deleted normalized row laws remain distinct.

Verification: `lake build Test.FiniteLocalLemma` passed 1,510 jobs with four
standard-only axiom audits (`propext`, `Classical.choice`, `Quot.sound`).
Persistent tests cover sharp independent events, a duplicate-event failure
of nonneighbor independence, zero events with zero parameters, exclusion
of parameter one, and the arbitrary-event extension. The separate row-law
tests passed 1,723 jobs and five standard-only audits, including a concrete
shared-row negative control and empty selected-row sets.
