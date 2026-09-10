# Fixed K=4 rational coefficient vectors

[finite_k4_fixed_seeds.json](finite_k4_fixed_seeds.json) contains two rational
vectors in the universal sorted 407-role order. Its SHA-256 is
`9965af6588dc453411d02abcbf4d23f94d553895532e45d5df995278a6408139`.
Each vector satisfies 91 quintic coefficient equations. The respective target
values are 5424/15625 for n=5 and 14805351/16000000 for n=20.
Both equal 2a−a² for a=(n)₄/n⁴.

The role catalogue enumerates the 52 restricted-growth equality partitions
of five positions and the 6×2 permutations of the multiplier triple and
quadratic pair. Unencoded tuple keys are sorted lexicographically and packed
in base 25. All 407 keys are checked against the
[quintic template](FINITE_K4_QUINTIC_SOURCE.md); positions are not identified
merely by vector length. Row-column transposition is not quotiented out.

The [generator](../scripts/generate_finite_k4_fixed_seeds.py) reads the included
JSON as literal rational data. It rejects floating-point, Boolean, nonreduced
and zero-denominator coefficients, and checks role order, case coverage and
every coefficient equation. Negative rational coefficients are retained.
Normal regeneration uses only files in this repository.

[FiniteK4FixedSeedEquations](../DR/Certificates/FiniteK4FixedSeedEquations.lean)
checks the actual finite sparse row terms and transfers the equations from
ℚ to ℝ. [The block certificates](FINITE_K4_FIXED_BLOCKS_SOURCE.md) provide the
separate positivity and kernel statements needed for the probability bounds.

```sh
python3 scripts/generate_finite_k4_fixed_seeds.py --check
python3 -O scripts/generate_finite_k4_fixed_seeds.py --check
python3 scripts/test_finite_k4_fixed_seeds.py
lake --wfail build +DR.Certificates.FiniteK4FixedSeedEquations +Test.FiniteK4FixedSeeds
```

The tests reject altered coefficients, target constants, and zero-vector
replacements. Coefficient identities alone do not imply matrix positivity.
