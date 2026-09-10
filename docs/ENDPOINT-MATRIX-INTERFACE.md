# Endpoint collision matrix estimate

A completion of squares gives a uniform lower bound for a diagonal
matrix plus two low-rank terms. The criterion below applies to arbitrary
real vectors; its endpoint application substitutes localized collision
loads and the normalized elementary coefficient.

For `m ≥ 3`, real vectors `s,t,v`, and real `sigma`, define

```
Q(i,j) = (if i=j then 1+t(i)-2v(i) else 0)
           + sigma*s(i)*s(j)-1-t(i)-t(j).
```

The theorem `endpoint_collision_lower_matrix_gap` proves, for every real `x`,

```
(3/32) * sum_i x(i)^2 ≤ xᵀ Q x
```

from these explicit assumptions:

- `t(i) ≥ 0` for every row;
- `sum_i (1-m*s(i))^2 ≤ 1/9`;
- `theta = sum_i t(i)/m ≤ 1/4`;
- `sum_i (t(i)-theta)^2 ≤ 1/64`;
- `v(i) ≤ 1/4` for every row;
- `sigma ≥ 4*m^2`.

No assumption `sum_i s(i)=1` is needed. All real vectors, zero vectors,
and negative `v` entries are retained. Neither positivity of `Q` nor the
endpoint maximizer conclusion is taken as a premise.

The proof sets `e=1-m*s`, `ell=t-theta`,
`kappa=sigma-m^2*(1+2*theta)`, and `g=(1+2*theta)*e+ell`.
An exact completion retains the positive square with coefficient `kappa`.
The assumptions give `kappa ≥ (5/2)*m^2 > 0`; Cauchy–Schwarz bounds the
remaining negative terms, leaving

```
1/2 - 1/6 - 1/12 - (2/5)*(5/8)^2 = 3/32.
```

The probability side supplies the normalized localized doubleton and
deficit-two loads. The actual deletion expectation is constructed in
[RowDeletionExpectation](../DR/Endpoint/RowDeletionExpectation.lean).
The [rook normalization](ENDPOINT-ROW-DELETION-ROOK.md) identifies
`sigma = E/(gamma*p0)`. The [actual kernel theorem](ENDPOINT-ACTUAL-KERNEL-POSITIVITY.md)
transfers this lower bound to the averaging kernel. The endpoint strip
proofs then derive the scalar bounds from the contender inequality.

## Formal statements

[CollisionSquareCompletionScalar](../DR/Endpoint/CollisionSquareCompletionScalar.lean), [CollisionSquareCompletion](../DR/Endpoint/CollisionSquareCompletion.lean).
