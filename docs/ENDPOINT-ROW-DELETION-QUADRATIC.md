# Quadratic bounds for actual deletion patterns

For the deletion matrices associated with the four possible collision
patterns, exact identities and weighted 2xy≤x²+y² estimates give
lower bounds for the negative quadratic form.

For any symmetric matrix with nonnegative entries, its quadratic form is
at most the sum of its row sums times the corresponding coordinate squares.
The proof sums `2xy ≤ x²+y²` with the actual matrix entries as weights.
Vectors may have arbitrary real signs; symmetry and entry nonnegativity
are explicit hypotheses of this reusable statement.

For an exact tripleton, the actual deletion matrix has row sum two on its
three rows and zero elsewhere. For two exact disjoint doubletons it has
row sum two on their union and zero elsewhere. These identities prove the
required lower bounds for the negative deletion quadratic form. No
spectral bound or collision probability estimate is assumed.

For an exact single doubleton, the module proves the complete quadratic
identity with the square of its incidence-weighted coordinate sum retained.
The lower bound drops precisely that nonnegative square. For an injective
assignment it proves the exact identity-minus-ones form.

## Formal statements

[RowDeletionQuadratic](../DR/Endpoint/RowDeletionQuadratic.lean).
