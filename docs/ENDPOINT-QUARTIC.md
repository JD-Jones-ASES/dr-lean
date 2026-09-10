# Quartic endpoint strip

`uniform_maximum_quartic_endpoint_strip` proves that the uniform probability
board is the unique maximizer for every endpoint `K=m` with `m>=16` and
`N>=20000*m^4`, together with the transposed rectangle. The domain is the full
closed probability simplex, including zero cells, rows, and columns.

The proof formalizes the corresponding accepted P0174 endpoint range from
Analytic-Lab. It combines the [global linear leading-gauge modulus](ENDPOINT-COARSE-GAUGE.md)
with the [actual contender concentration](ENDPOINT-LONG-COLUMN-CONCENTRATION.md).
Writing `V=sum_i(r_i-1/m)^2`, `a=m!/m^m`, and `b=(m-2)(m+1)/2`, these give
`V<503*b/N` and every column mass less than `25/N`. The exact scalar cutoff
then gives `m^2*V<1/16`. The [retained-kernel closure](ENDPOINT-LONG-COLUMN-CLOSURE.md)
derives positive definiteness for every contender and supplies the global
maximum and unique equality. No row or column concentration is assumed in
the final theorem.

`Test.Quartic` checks the first dimension and exact column cutoff, transpose,
a larger rectangle, explicit inequality and equality statements, and a
nonzero scalar variance. Negative controls reject rounding either cutoff
down and show failure of the scalar implication after dropping its column
bound. Three axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

Replay: `lake --wfail build Test.Quartic`.
