# Leading norm and uniform normalization

The leading gauge is the sum of the column lengths measured by the
complementary-product matrix B(r). At uniformity its value is
√(1−m!/m^m). For a positive semidefinite B(r), the triangle inequality
compares this column sum with the quadratic length of the row-mass vector.

For m≥2 and n>0, the uniform gauge is exactly `sqrt(1−m!/m^m)`, with a factor `1/n` for each
column cost. The marginal quadratic is `sum(r)^2−m!*product(r)` for arbitrary
signed rows, including zero coordinates. AM–GM gives the exact scale bound
`gamma≤alpha/[m(m−1)]` on nonnegative mass-one rows, where
`gamma=(m−2)! product(r)` and `alpha=m!/m^m`.

The finite norm comparison proves quadratic Cauchy–Schwarz by applying
Mathlib's discriminant theorem to the actual quadratic along a line.
It sums the resulting bilinear bounds to obtain the triangle inequality
for any positive semidefinite real form. Singular forms, signed vectors,
and empty families are included. Applied to the actual board columns, it
gives `G(P)≥sqrt(1−m!*product(rowSum(P)))` when the original leading kernel
is positive semidefinite. That positivity remains an explicit hypothesis;
the kernel is not positive on every probability board.

## Formal statements

[LeadingConstants](../DR/Endpoint/LeadingConstants.lean), [LeadingUniform](../DR/Endpoint/LeadingUniform.lean), [LeadingNorm](../DR/Endpoint/LeadingNorm.lean).
