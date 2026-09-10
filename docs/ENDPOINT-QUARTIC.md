# Quartic endpoint strip

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`uniform_maximum_quartic_endpoint_strip` proves that the uniform probability
board is the unique maximizer for every endpoint `K=m` with `m>=16` and
`N>=20000*m^4`, together with the transposed rectangle. The domain is the full
closed probability simplex, including zero cells, rows, and columns.

Combine the [global linear leading-gauge modulus](ENDPOINT-COARSE-GAUGE.md)
with the [actual contender concentration](ENDPOINT-LONG-COLUMN-CONCENTRATION.md).
Writing `V=sum_i(r_i-1/m)^2`, `a=m!/m^m`, and `B=(m-2)(m+1)/2`, these give
`V<503*B/N` and every column mass less than `25/N`. The exact scalar cutoff
then gives `m^2*V<1/16`. The [retained-kernel closure](ENDPOINT-LONG-COLUMN-CLOSURE.md)
derives positive definiteness for every contender and supplies the global
maximum and unique equality. No row or column concentration is assumed in
the final theorem.

## Formal statements

[Quartic](../DR/Endpoint/Quartic.lean).
