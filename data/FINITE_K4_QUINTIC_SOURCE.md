# K4 quintic coefficient template

`finite_k4_quintic_template.json` is finite mathematical data reconstructed by
`scripts/generate_finite_k4_quintic.py`. It contains all 52 equality patterns on
five positions, all 407 roles for an unordered multiplier triple and an ordered
quadratic pair, and the 91 lexicographically ordered quintic monomial equations.
The four-row restriction has 84 equations; the four-square restriction has 78.
This is a coefficient-identity catalogue. It makes no PSD or endpoint claim.

The mathematical source is Analytic-Lab P0174
`QUINTIC_CERTIFICATES_K4.md`, section “Complete coefficient catalog and literal
counting”, and the literal formula documented by `quintic_certificate.py`'s
`_template`. The generator never imports or executes the Lab implementation.
It uses this project's frozen first-position pattern and role-key conventions.

The primary coefficient reconstruction chooses each distinct multiplier
multiset once and counts one or two orders of its remaining pair. An independent
audit enumerates every distinct order of the whole five-cell monomial and weights
it by the product of the triple-multiplicity factorials divided by six. These
two exact integer rows agree. The source success count is the number of distinct
orders whose first four row labels or first four column labels are distinct.

For every one of the 2704 pattern pairs, the generator verifies the ten-choice
identity: multiplicity times each sum of local weights equals 60 times its
literal source row coefficient. The local weights are six, two and one for a
constant triple, one repeated pair, and three distinct cells. Separately,
multiplicity times 12 times the sum of the five deletion-success bits equals
60 times the source success count. No transpose quotient is used. All 407 roles
occur in exactly one sparse row; there are 407 terms total, at most ten per row.
Padded ten-term rows use `(0,0)` for unused slots. Each local choice selects
its actual nonpadding role slot, and every slot satisfies the exact weighted
fiber equation. Unused slots have empty fibers, including the singleton case.

All 84 restricted equations, multiplicities and successes are independently
compared with the frozen four-row generator's mathematical catalogue at
`scripts/data/four_row_finite/catalogue.json`. The optional source audit reads
the pinned rational JSON and verifies every coefficient equation for the four
literal source cases 4×5, 4×50, 4×1000 and 20×20. This audit does not check their
Gram matrices and does not certify those endpoint inequalities.

Pinned source SHA-256 values:

- `quintic_certificate.py`: `00a675fdbf9ca8de469d1628484a3331eaed1abcd82cfaffcb22bab8ea033a56`
- `QUINTIC_CERTIFICATES_K4.md`: `2aef864ddac9f491167344e4e619da48042f39e0cb01bbc91ee2d6b50d5a9a94`
- `quintic_k4_coefficients.json`: `206e590b543473de13b2a6b969cdcbe6fae2526d3f12a1408083b6713c0f9c40`

Reproduce both generated files, including all exact counting checks:

```sh
python3 scripts/generate_finite_k4_quintic.py --check
python3 -O scripts/generate_finite_k4_quintic.py --check
python3 scripts/test_finite_k4_quintic.py
python3 -O scripts/test_finite_k4_quintic.py
```

For the optional read-only external source audit, add `--audit-source` followed
by the named P0174 source directory. Ordinary reproduction does not require the
Lab checkout. Corruption controls retain missing, extra, repeated, reordered and
noninteger data, wrong multiplicity corrections, changed coefficient/event
counts, wrong source hashes and changed generated output. Python checks use
explicit exceptions and remain active under `python -O`. Lean's separate checked
semantic bridge is required to turn these definitions into the actual signed
quintic identity; generation alone supplies no theorem.
