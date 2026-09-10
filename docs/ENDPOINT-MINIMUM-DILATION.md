# Minimum rectangular dilation

Let m,n>0 and let P be a nonnegative m×n matrix of total mass one.
A balanced probability board has row sums 1/m and column sums 1/n.
[MinimumDilation](../DR/Endpoint/MinimumDilation.lean) constructs such a
board dominated by a positive multiple of P. It takes the finite
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

For each positive cut, q≤cutMass(P,I,J)/p ensures that the capacities
P/q satisfy the balanced transport criterion. The finite minimum attains
one of these ratios. The [rectangular transport theorem](../DR/Endpoint/RectangularTransport.lean)
therefore constructs B. At a minimizing cut, the identity
cutMass(B,I,J)=p+cutMass(B,Iᶜ,Jᶜ), together with qB≤P, forces the
complementary mass to vanish. This is the minimum-dilation method of
Cheon and Wanless, [Some results towards the Dittert conjecture on permanents](https://users.monash.edu.au/~iwanless/papers/DittertIndecompLAA.pdf),
Lemma 2.3; their domination criterion credits C.-K. Li.

## Formal statements

[MinimumDilation](../DR/Endpoint/MinimumDilation.lean), [RectangularTransport](../DR/Endpoint/RectangularTransport.lean), [CutDeficit](../DR/Endpoint/CutDeficit.lean).
