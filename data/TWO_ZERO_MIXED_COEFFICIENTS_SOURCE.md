# Mixed quadratic coefficients and repeated-row permanents

For a signed (n+2)×(n+2) matrix A, take the product of its column linear forms
in row variables, `matrixProductPolynomial A.transpose`. Extract exponent one
in each of the first n variables with `capacityReduce`. The two surviving
variables correspond to the final two rows. Their coefficients are:

- (2,0): the permanent after repeating the penultimate row, divided by two;
- (1,1): the original permanent;
- (0,2): the permanent after repeating the final row, divided by two.

[TwoZeroMixedCoefficients](../DR/Endpoint/TwoZeroMixedCoefficients.lean) proves
all three identities for arbitrary signed entries, including n=0. Elimination
commutes with substitution in the surviving variables. Repeating row u into
row v is the substitution Xᵤ↦Xᵤ+Xᵥ, Xᵥ↦0. Expansion of an actual homogeneous
bivariate quadratic proves the factor two.

The [stable quadratic discriminant](../DR/Endpoint/StableQuadratic.lean) and
[its matrix application](../DR/Endpoint/TwoZeroMixedStability.lean) give
`permanent_repeated_rows_inequality` for every entrywise nonnegative matrix,
including zero rows and columns. These inequalities support the
[two-zero face reduction](../DR/Endpoint/TwoZeroReduction.lean).

```sh
lake --wfail build Test.TwoZeroMixedCoefficients
```

Tests retain signed 3×3 coefficient identities, the empty eliminated prefix,
row substitution, and zero matrices. A signed matrix with permanent zero but
both repeated-row permanents two shows why the inequality needs nonnegativity.
