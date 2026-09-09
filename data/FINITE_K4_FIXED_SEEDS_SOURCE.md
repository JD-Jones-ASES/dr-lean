# Fixed K4 coefficient seeds

This package contains two exact rational vectors, in the universal sorted
407-role order, and checks their 91 quintic coefficient equations each. It
supplies the coefficient-identity input for separate matrix certificates.
It does not prove a matrix positive semidefinite or establish an endpoint
maximum by itself.

The mathematical inputs are the P0174 sources in Analytic-Lab:

- `K4_FIVE_BY_FIVE.md`: the single literal `SEED` tuple in the first Python
  heredoc, for the 5×5 value `5424/15625`.
- `quintic_k4_coefficients.json`: the single `(20,20)` case, for the value
  `14805351/16000000`.
- `quintic_certificate.py`: read-only attribution and pinned description of
  the sorted role convention; its code is never imported or executed here.

Exact source SHA-256 digests:

| Source | SHA-256 |
| --- | --- |
| K4_FIVE_BY_FIVE.md | `2276d83d8dba5cfdcbd7f10e050fbbcd2cef3e03c6e6dd222e18970744713418` |
| quintic_k4_coefficients.json | `206e590b543473de13b2a6b969cdcbe6fae2526d3f12a1408083b6713c0f9c40` |
| quintic_certificate.py | `00a675fdbf9ca8de469d1628484a3331eaed1abcd82cfaffcb22bab8ea033a56` |
| Local quintic template JSON | `170599056c8468ec4318e988d4dd81246251379af0550c159ab5235b94fee690` |

The generator independently enumerates the 52 restricted-growth equality
partitions and all 6×2 permutations within the multiplier-triple and quadratic
pair roles. It sorts the unencoded tuple keys lexicographically, packs them in
base 25, and compares all 407 keys against the frozen Lean template. Thus the
source vector positions are not identified by length alone. No transpose
quotient is introduced. Exact arithmetic also checks both constants against
`2*a-a²`, where `a=(n)_4/n⁴`.

The Markdown extractor uses `ast.parse` only to find the unique top-level seed
assignment and `ast.literal_eval` to read that literal. Function calls, alias
assignments, missing or duplicate seeds, and non-tuple literals are rejected.
JSON is read as data. Floating-point, Boolean, nonreduced, and zero-denominator
coefficients are rejected. Source hashes, case coverage, role order, and every
coefficient equation are independently checked during regeneration. Negative
rational matrix coefficients are intentionally retained.

The checked-in `data/finite_k4_fixed_seeds.json` is the self-contained literal
input for normal reproduction. To additionally replay the pinned extraction:

```bash
python3 scripts/generate_finite_k4_fixed_seeds.py --check
python3 -O scripts/generate_finite_k4_fixed_seeds.py --check
python3 scripts/generate_finite_k4_fixed_seeds.py --check --source-dir /path/to/P0174_rybin_semimatchings
python3 -O scripts/generate_finite_k4_fixed_seeds.py --check --source-dir /path/to/P0174_rybin_semimatchings
python3 scripts/test_finite_k4_fixed_seeds.py
python3 -O scripts/test_finite_k4_fixed_seeds.py
lake --wfail build +DR.Certificates.FiniteK4FixedSeedEquations +Test.FiniteK4FixedSeeds
```

The Lean checks operate on the actual finite sparse row terms, then transport
all equations from ℚ to ℝ. Kernel-checked lengths preserve the literal vectors.
The persistent tests reject changed coefficients, changed target constants,
and a zero-vector replacement. Theorems about physical matrix positivity,
constant kernels, and the global probability maximum are separate obligations.
