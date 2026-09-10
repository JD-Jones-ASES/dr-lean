# Actual reduction of the two-independent-zero face

For every doubly stochastic matrix of order n+2 with n positive and any two
zeros in distinct rows and columns, `twoZeroReducedBoard_representative`
produces parameters 0 <= a,b <= 1/n whose actual reduced matrix permanent is
at most the input permanent. Additional zeros are allowed everywhere.

The reduced matrix has leading diagonal 1-na, 1-nb, leading off-diagonal
zeros, repeated border entries a and b, and an ordinary n-by-n block whose
entries are (1-a-b)/n.

The proof chooses a minimum of the actual permanent on the entire compact
face, then minimizes its squared Frobenius norm among all those minima. The
previous support theorem supplies positive cofactors. Allowed cofactor
comparisons and the unconditional Alexandrov permanent inequality show that
averaging rows with identical allowed support preserves the permanent.
The exact squared-norm change forces such rows to agree at the chosen
minimizer. Transposition gives the corresponding column statement. The doubly
stochastic row and column equations then force the displayed reduced form
and its full closed parameter rectangle.

Arbitrary prescribed zeros are moved to the leading off-diagonal positions
by independent permutations of the actual finite row and column types. The
permanent, all marginal equations, and every additional zero are retained.

This formalizes the repeated-support reduction used in
[Pula, Song and Wanless (2011)](https://cs.du.edu/~mathfiles/preprints/nsm-math-preprint-1022.pdf)
through the separately proved stable-quadratic version of Alexandrov's
inequality. It assumes no external face-minimizer or averaging theorem.

The exact permanent calculation is proved in
`DR/Endpoint/TwoZeroReducedCounting.lean`. Together with the closed scalar
polynomial bounds it yields the [actual two-zero floor](TWO_ZERO_PERMANENT.md),
which closes the [square near-endpoint theorem](SQUARE_NEAR_ENDPOINT.md).

Run `lake build +Test.TwoZeroReduction`. Tests retain signed averaging, repeated
selected indices, empty faces and empty dimensions, boundary parameters,
ordinary row/column symmetry, and the full actual representative statement.
