# K=4 quintic coefficient template

[finite_k4_quintic_template.json](finite_k4_quintic_template.json) records all
52 equality patterns on five positions, 407 roles for an unordered multiplier
triple and ordered quadratic pair, and 91 lexicographically ordered quintic
monomial equations. Restriction to four rows gives 84 equations; restriction
to a 4×4 square gives 78. Its SHA-256 is
`170599056c8468ec4318e988d4dd81246251379af0550c159ab5235b94fee690`.

The [generator](../scripts/generate_finite_k4_quintic.py) chooses each distinct
multiplier multiset once and counts the one or two orders of its remaining
pair. A second count enumerates every distinct order of the five-cell monomial,
weighted by the triple-multiplicity factorials divided by six. The two exact
integer rows agree. Success means that the first four row labels are distinct
or the first four column labels are distinct, with the overlap counted once.

For all 2,704 pattern pairs, ten local choices reconstruct the exact row
coefficient. Local triple weights are six, two and one according as the triple
is constant, has one repeated pair, or has three distinct cells. Multiplicity
times each local-weight sum equals 60 times its row coefficient. Separately,
multiplicity times 12 times the sum of the five deletion-success indicators
equals 60 times the success count. No transpose quotient is used.

All 407 roles occur in exactly one sparse row; there are 407 terms in total
and at most ten per row. Unused slots are (0,0), with empty local-choice fibers.
The 84 four-row equations also agree with the included
[four-row catalogue](../scripts/data/four_row_finite/catalogue.json).

The [Lean template](../DR/Certificates/FiniteK4QuinticTemplate.lean) and
[local identity](../DR/Certificates/FiniteK4QuinticLocal.lean) prove the
coefficient semantics. These identities are distinct from the Gram conditions
required for the actual probability inequality.

```sh
python3 scripts/generate_finite_k4_quintic.py --check
python3 -O scripts/generate_finite_k4_quintic.py --check
python3 scripts/test_finite_k4_quintic.py
python3 -O scripts/test_finite_k4_quintic.py
```

Regeneration uses the included data. Tests reject missing, repeated, reordered
or noninteger terms, wrong multiplicity factors and changed event counts.
