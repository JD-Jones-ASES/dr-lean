# Saturated stationary row stability

The three modules [SaturatedScalarBounds](../DR/Endpoint/SaturatedScalarBounds.lean),
[SaturatedRows](../DR/Endpoint/SaturatedRows.lean), and
[SaturatedStationary](../DR/Endpoint/SaturatedStationary.lean) formalize
sections 1–3 of the accepted P0174 `ENDPOINT_SATURATED_STABILITY.md` argument.
The final theorem consumes the actual leading-gauge moment and stationarity
identities proved in [LeadingMoments](../DR/Endpoint/LeadingMoments.lean).
It does not treat stationarity as a consequence of an arbitrary probability board.

For positive mass-one rows and `0<a<1/1000`, the minimum comparison
`G≤sqrt(1−a)+a/1000` and weighted Cauchy inequality give `D>499a/1000`.
The saturated derivative `t=a m²/[1000(1+m²ν)²]` controls every pair by
`2t r_i r_j≤4a/1000`, without a small-variance assumption. Subtracting the
stationarity equations and using the exact derivative cap gives reciprocal
spread less than `1184/121`.

Weighted averaging of all reciprocal pair inequalities gives the actual
row interval. Summing the positive products of distances to its endpoints
yields `ν<L²/[m(m²−L²)]`. The exact polynomial after shifting `m=u+96` has
strictly positive coefficients `14626359,1406404928,219750400`.
Together with the actual leading-scale bound, this proves strict positivity
of the original complementary-product kernel and `r_i<2/m` for every `m≥96`.
The subsequent product gap and global minimization argument are separate.

`lake --wfail build Test.SaturatedStationary` passed 2,396 jobs, twelve
examples and thirteen standard-only axiom audits, with warnings rejected.
Controls include a rejected sufficient threshold of 95, signed row inputs
for the pointwise square bound, a nonuniform physical row vector, omission
of mass normalization, a nonzero-variance penalty, exact rational moment
data, and actual kernel positivity at uniform96 rows. No new P2 principal
target is asserted by this scalar foundation alone.
