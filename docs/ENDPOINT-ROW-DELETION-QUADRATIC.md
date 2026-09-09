# Quadratic bounds for actual deletion patterns

`DR/Endpoint/RowDeletionQuadratic.lean` proves the pointwise quadratic
ingredients of P0174 `ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`, Section 1.

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

Replay: `lake build Test.RowDeletionQuadratic`. Controls show the sharp
factor two on both K3 and K2,2, refute replacement by one, check a mixed-sign
single-pair vector, and retain an empty finite host. Averaging these actual
pointwise statements and connecting them to the deleted-board rook kernel
remain separate proof obligations.
