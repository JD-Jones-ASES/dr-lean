# Endpoint collision matrix estimate

The matrix estimate is proved in
[CollisionSquareCompletion](../DR/Endpoint/CollisionSquareCompletion.lean),
using the exact scalar completion in
[CollisionSquareCompletionScalar](../DR/Endpoint/CollisionSquareCompletionScalar.lean).
The source is Analytic-Lab P0174 `ENDPOINT_LOCALIZED_COLLISION_KERNEL.md`,
sections 2 and 3. This is a matrix criterion; the accepted endpoint parameter
ranges still require the actual contender and rook normalization arguments.

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

No assumption `sum_i s(i)=1` is needed. All real test vectors, zero vectors,
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

[The persistent tests](../Test/CollisionSquareCompletion.lean) include seven
examples: exact attainment of the scalar estimate, rejection of an enlarged
`1/8` margin, signed and zero vectors, and explicit negative quadratic forms
when the `v` or `sigma` bound is dropped. The targeted build passed 1,856 jobs
with three axiom audits using only `propext`, `Classical.choice`, and
`Quot.sound`, and no warnings.

The probability side supplies the normalized localized doubleton and
deficit-two loads. The actual deletion expectation is constructed in
[RowDeletionExpectation](../DR/Endpoint/RowDeletionExpectation.lean).
Actual endpoint use must still connect its normalization to
`sigma = E/(gamma*p0)` and establish the stated moment and numerical bounds
from a true contender in each accepted parameter range. This module alone
completes none of the remaining endpoint targets.
