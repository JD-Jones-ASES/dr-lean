# Minimum rectangular dilation

[MinimumDilation](../DR/Endpoint/MinimumDilation.lean) constructs a balanced
probability board from the original real capacities. It takes the finite
minimum of `cutMass(P,I,J)/p(I,J)` over all positive cut demands
`p=|I|/m+|J|/n−1`. Positive cuts must have positive actual mass; individual
cells may vanish. The whole cut supplies the upper bound one.

The result supplies `0<q≤1`, a balanced board `B` with `qB≤P`, and a positive
active cut with `cutMass(P,I,J)=qp`. The exact balanced complement identity
then forces the complementary rectangle of `B` to have zero mass. This is
the minimum amplification, equivalently the maximum admissible balanced
dilation: every competing nonnegative factor is at most the active ratio.
Unit dilation identifies the original board with its balanced board by
equal total mass. No permanent-minimizer theorem is assumed.

The proof is the finite-cut construction used by the accepted P0174 active-cut
endpoint arguments. Its dependencies are the internally proved real
[rectangular transport theorem](../DR/Endpoint/RectangularTransport.lean) and
[cut identities](../DR/Endpoint/CutDeficit.lean).

`lake --wfail build Test.MinimumDilation` passed 2,423 jobs, eight examples,
and six standard-only axiom audits. The tests use a strictly positive 3-by-3
board whose optimal balanced dilation is 7/8 and whose balanced board gains
a zero cell. They instantiate the finite existence theorem over all cuts,
bound every competitor using the physical active cut, retain unit dilation,
and reject positive dilation when an original row is zero. These are geometry
checks; the separate permanent and probability arguments remain downstream.
