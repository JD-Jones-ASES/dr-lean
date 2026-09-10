# Combined endpoint strip for every m >= 5

`uniform_maximum_combined_endpoint_strip` proves the accepted range
`m >= 5`, `N >= 100000000000*m^2`, `K=m`, together with its transpose.
Every nonnegative probability board is included, and equality holds if
and only if the board is uniform. The exact maximum is
`a_m + (1-a_m)*(N)_m/N^m`, where `a_m=m!/m^m`.

The source is Analytic-Lab P0174's `ENDPOINT_COLLISION_CLUSTER_STRIPS.md`,
combined with the leading-gauge and polynomial-strip notes cited there.
Astra implemented the small-row proof and exact dispatcher. The root
agent supplied the frozen larger-row strips and the common collision,
deleted-row, scalar absorption and endpoint-rigidity foundations.

The formal proof has three branches:

- `5 <= m <= 15`: the new direct small-row argument below.
- `16 <= m <= 95`: the [quartic strip](ENDPOINT-QUARTIC.md), using the
  exact comparison `20000*m^4 <= 10^11*m^2`.
- `m >= 96`: the [quadratic strip](ENDPOINT-QUADRATIC.md).

The accepted combined range is unchanged. The small-row proof directly
uses this cutoff; it does not claim a separate formalization of the
older `100000*m^7` endpoint range.

## Actual small-row contender concentration

`RepeatedCellConcentration` identifies equality of two specified complete
samples as a genuine simultaneous row/column failure witness. For every
endpoint contender it proves

```
(colSum P j)^2 <= m * sum_cells P_cell^2 <= m*choose(m,2)/N.
```

`SmallRowConcentration` uses this estimate for the first cap. At
`5 <= m <= 15` and the accepted cutoff, it proves `c_j < 1/1000`, hence
`b*c_j < 1/6`, where `b=(m-2)(m+1)/2`. Eleven ordinary kernel rational
checks prove the two small-factorial guards `a*b<1` and `25*b*a^2<1`;
the actual rho bound gives `b*rho^2<1`.

The [actual contender comparison](ENDPOINT-LEADING-COMPARISON.md), the
[global coarse gauge](ENDPOINT-COARSE-GAUGE.md), and the root's scalar
variance absorption then imply `c_j < 25/N` and
`V <= 75500*b/N`, where `V=sum_i(r_i-1/m)^2`. The exact small-row cutoff
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

`LongColumnKernelFive` and `LongColumnClosureFive` reuse the root's common
collision-cluster and centered-deletion arguments with that stronger
coefficient. Actual deletion gives positive retained rows, collision
intensity at most `1/12`, and `p_del>=11/12`. The kernel is positive
definite, so every unequal column pair can be improved. The established
one-sided endpoint rigidity theorem then proves the full maximum and
its exact equality condition, including zero cells and columns.

## Verification

`lake --wfail build Test.Combined` passed 3348 jobs with nineteen persistent
examples and eleven standard-only axiom audits, without warnings. The tests cover
both dispatcher boundaries, the first dimension, the exact closed column
cutoff, transpose, explicit inequality and iff equality, a genuine
repeated-cell implication, failure at one draw, signed homogeneity,
the zero-degree elementary sum, a literal uniform retained-board coefficient,
exact factorial guards, and a negative
small-dimension factorial control. Eleven axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. There are no new axioms,
`sorry`, or native-evaluation certificate gates.
