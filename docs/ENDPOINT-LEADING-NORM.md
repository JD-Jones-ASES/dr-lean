# Leading norm and uniform normalization

`LeadingConstants`, `LeadingUniform`, and `LeadingNorm` provide three inputs
to the accepted P0174 `ENDPOINT_LEADING_GLOBAL.md` and
`ENDPOINT_SATURATED_STABILITY.md` arguments. The factorial comparison is exact;
the exponential bound uses Mathlib's proved rational bound on `exp(1)`.
No numerical approximation is used in the proof.

The uniform gauge is exactly `sqrt(1−m!/m^m)`, with a factor `1/n` for each
column cost. The marginal quadratic is `sum(r)^2−m!*product(r)` for arbitrary
signed rows, including zero coordinates. AM–GM gives the exact scale bound
`gamma≤alpha/[m(m−1)]` on nonnegative mass-one rows.

The finite norm comparison proves quadratic Cauchy–Schwarz by applying
Mathlib's discriminant theorem to the actual quadratic along a line.
It sums the resulting bilinear bounds to obtain the triangle inequality
for any positive semidefinite real form. Singular forms, signed vectors,
and empty families are included. Applied to the actual board columns, it
gives `G(P)≥sqrt(1−m!*product(rowSum(P)))` when the original leading kernel
is positive semidefinite. That positivity remains an explicit hypothesis;
the kernel is not positive on every probability board.

`lake --wfail build Test.EndpointLeadingUniform` passed 3,242 jobs, fourteen
examples and eight standard-only axiom audits. Controls retain the empty
column count, signed and zero marginals, a singular form, an empty vector
family, and failure of nonnegativity for an indefinite form.
These are prerequisites, not a new endpoint principal theorem.
