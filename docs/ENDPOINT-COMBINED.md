# Combined endpoint strip for every m >= 5

For an m×n nonnegative matrix P of total mass one, let F_k(P) be the
probability that k independent cell draws have distinct rows or distinct
columns, with inclusive OR. Write U_ij=1/(mn) and (n)_m=n(n−1)…(n−m+1).
At the endpoint k=m, put a=m!/m^m and b=(n)_m/n^m. The sharp statement is
F_m(P)≤a+b−ab, with equality if and only if P=U. A contender means a
probability board satisfying F_m(P)≥F_m(U).

`uniform_maximum_combined_endpoint_strip` proves the range
`m >= 5`, `N >= 100000000000*m^2`, `K=m`, together with its transpose.
Every nonnegative probability board is included, and equality holds if
and only if the board is uniform. The exact maximum is
`a_m + (1-a_m)*(N)_m/N^m`, where `a_m=m!/m^m`.

The argument first proves concentration for matrices whose value is at
least the uniform value. It then shows that averaging any unequal pair
of columns strictly increases the objective. At a global maximum all
columns therefore agree, and the row-product equality forces uniformity.

The proof has three branches:

- `5 <= m <= 15`: the direct small-row argument below.
- `16 <= m <= 95`: the [quartic strip](ENDPOINT-QUARTIC.md), using the
  exact comparison `20000*m^4 <= 10^11*m^2`.
- `m >= 96`: the [quadratic strip](ENDPOINT-QUADRATIC.md).

For 5≤m≤15 the concentration estimates below apply directly at
N≥10^11m². For 16≤m≤95 the quartic cutoff follows from
20000m²≤20000·95²<10^11. For m≥96 the quadratic cutoff is immediate.

## Actual small-row contender concentration

`RepeatedCellConcentration` identifies equality of two specified complete
samples as a genuine simultaneous row/column failure witness. For every
endpoint contender it proves

```
(colSum P j)^2 <= m * sum_cells P_cell^2 <= m*choose(m,2)/N.
```

`SmallRowConcentration` uses this estimate for the first cap. At
`5 <= m <= 15` and the cutoff, it proves `c_j < 1/1000`, hence
`B*c_j < 1/6`, where `B=(m-2)(m+1)/2`. Eleven ordinary kernel rational
checks prove the two small-factorial guards `a*B<1` and `25*B*a^2<1`;
the actual rho bound gives `B*rho^2<1`.

The [actual contender comparison](ENDPOINT-LEADING-COMPARISON.md), the
[global coarse gauge](ENDPOINT-COARSE-GAUGE.md), and scalar
variance absorption then imply `c_j < 25/N` and
`V <= 75500*B/N`, where `V=sum_i(r_i-1/m)^2`. The exact small-row cutoff
therefore yields the required actual row budget `m^2*V < 1/16`.
No contender concentration or stationarity is assumed as a premise.

## Retained board and collision law

`LongColumnCoefficientFive` strengthens the common coefficient argument.
For a nonnegative retained board of mass `h>3/4`, column cap `25/N`, and
`N>=10000*m^2`, the normalized column law and the proved linear elementary
bound give

```
E = e_(m-2)(retained columns) >= h^(m-2)/(2*(m-2)!).
```

Exact homogeneous scaling returns this coefficient to the original
retained board. The factorial bound `a_m<=24/625<1/16` proves
`8*m^2*(m-2)! <= m^m` for all `m>=5`. AM-GM and the actual row-avoidance
factor thus yield the same coefficient ratio `E/(G*p_del)>=4*m^2` used
by the collision-cluster closure. Here `G=product(retained row masses)/h^2`;
`p_del` is explicitly the independent retained-row avoidance probability.
It is never replaced by the original-row law.

`LongColumnKernelFive` and `LongColumnClosureFive` reuse the common
collision-cluster and centered-deletion arguments with that stronger
coefficient. Actual deletion gives positive retained rows, collision
intensity at most `1/12`, and `p_del>=11/12`. The kernel is positive
definite, so every unequal column pair can be improved. The established
one-sided endpoint rigidity theorem then proves the full maximum and
its exact equality condition, including zero cells and columns.

## Formal statements

[RepeatedCellConcentration](../DR/Endpoint/RepeatedCellConcentration.lean), [SmallRowConcentration](../DR/Endpoint/SmallRowConcentration.lean), [LongColumnCoefficientFive](../DR/Endpoint/LongColumnCoefficientFive.lean), [LongColumnKernelFive](../DR/Endpoint/LongColumnKernelFive.lean), [LongColumnClosureFive](../DR/Endpoint/LongColumnClosureFive.lean), [Combined](../DR/Endpoint/Combined.lean).
