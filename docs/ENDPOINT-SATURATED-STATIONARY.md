# Saturated stationary row stability

The leading-gauge moment identities and stationarity equations imply
a row-spread bound at a minimum of the saturated penalized gauge.
The stationarity assumptions are derived at that minimum in
[LeadingMoments](../DR/Endpoint/LeadingMoments.lean); they are not
properties of arbitrary probability boards.

Write ν=∑_i(r_i−1/m)² and a=m!/m^m; let G,D,A_i be the
[leading-gauge moments](ENDPOINT-LEADING-STATIONARITY.md).
For positive mass-one rows and `0<a<1/1000`, the minimum comparison
`G≤sqrt(1−a)+a/1000` and weighted Cauchy inequality give `D>499a/1000`.
The saturated derivative `t=a m²/[1000(1+m²ν)²]` controls every pair by
`2t r_i r_j≤4a/1000`, without a small-variance assumption. Subtracting the
stationarity equations and using the exact derivative cap gives reciprocal
spread less than `1184/121`.

Weighted averaging of all reciprocal pair inequalities gives the actual
row interval, with L=1184/121. Summing the positive products of distances to its endpoints
yields `ν<L²/[m(m²−L²)]`. The exact polynomial after shifting `m=u+96` has
strictly positive coefficients `14626359,1406404928,219750400`.
Together with the actual leading-scale bound, this proves strict positivity
of the original complementary-product kernel and `r_i<2/m` for every `m≥96`.
The subsequent product gap and global minimization argument are separate.

## Formal statements

[SaturatedScalarBounds](../DR/Endpoint/SaturatedScalarBounds.lean), [SaturatedRows](../DR/Endpoint/SaturatedRows.lean), [SaturatedStationary](../DR/Endpoint/SaturatedStationary.lean).
