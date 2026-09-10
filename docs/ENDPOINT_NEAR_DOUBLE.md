# Exact near-square and doubled endpoint ranges

The exported theorems are the full sharp iid separation-probability
inequality with uniform equality if and only if the board is uniform:

- `uniform_maximum_short_endpoint`: `m≥117`, `m≤n≤2m`, sample order `m`;
- `uniform_maximum_double_endpoint`: `m≥80`, `n=2m`, sample order `m`.

Both theorems include transposition and the entire closed probability
simplex. They discharge the scalar hypotheses of the proved arithmetic
boundary-scaling theorem. No transport, positivity, or local-maximizer
assumption remains in either public statement.

## Sources and shared recurrence

The accepted ranges and exact bases are from the Lab notes
`P0174_rybin_semimatchings/PANG_RECTANGULAR_ENDPOINT.md` and
`P0174_rybin_semimatchings/ENDPOINT_ARITHMETIC_SCALING.md`.
The proof below retains their factorial recurrence and uses a common
rational bound for the two polynomial weights.

Write `a_m=m!/m^m`, `b_m=(2m)_m/(2m)^m`, and

```
W_p(m) = m^p (2m-1)^2 b_m + m^p (2m-1)^3 a_m.
```

The exact factorial identity gives

```
b_(m+1) * ((m+1)/m)^m = ((2m+1)/(m+1)) * b_m.
```

The degree-two binomial lower bound proves
`((m+1)/m)^m ≥ 5/2 - 1/(2m) ≥ 12/5` for `m≥5`. Thus
`b_(m+1) ≤ (5/6)b_m`. The separately proved factorial bound gives
`a_(m+1) ≤ a_m/2 ≤ (5/6)a_m`.

For `m≥80`, each of the weight factors `m` and `2m-1` grows by at
most `80/79`. For total exponent at most eight, the weight therefore
grows by at most `(80/79)^8 < 6/5`. Combining these estimates proves
`W_p(m+1) ≤ W_p(m)` for every integer `m≥80` and `p≤5`.
This is an all-dimension theorem, followed by induction from each base.

The two exact rational base comparisons, checked by Lean's kernel, are

```
W_5(117) < (39/40)(128/289),
W_3(80)  < (91/100)(128/289).
```

For fixed sample order `m`, the actual uniform avoidance factor is
monotone in the number of columns; its finite product proves this
directly. All other nonnegative column-count factors in the gain-one
criterion are also monotone, so the first base and recurrence cover the
whole interval `m≤n≤2m`. For doubled boards the arithmetic gain is
exactly `m`, reducing the weight exponent from five to three.

## Files and verification

`DoubleRecurrence` proves the factorial, binomial, decay, and column
monotonicity steps. `DoubleWeights` proves the common weighted induction.
`NearSquareParameters` and `DoubleParameters` prove the actual scalar
inequalities; `NearSquare` and `Double` connect them to boundary scaling.

Run `lake --wfail build Test.EndpointNearDouble`. The tests include
the recurrence at its first admissible dimension, both closed interval
endpoints, the smaller doubled threshold, transposition, full-simplex
equality, and strictness of every zero-entry board. Exact negative
controls show that the stated criterion fails at the threshold
predecessors and at `80×160` if the arithmetic gain is omitted. Those
controls do not assert that P2 fails there. Eleven axiom audits expose
only the standard Lean axioms.
