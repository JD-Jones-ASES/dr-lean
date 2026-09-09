# Four samples on every four-row rectangle

For every integer N≥4, the uniform matrix uniquely maximizes the probability
of distinct rows or distinct columns among four iid cell draws on a 4×N
probability board. Arbitrary marginals and zero entries are included. The
same theorem holds on N×4 boards. The exact maximum is

```
1 - (29/32) * (6/N - 11/N^2 + 6/N^3).
```

The single release declaration
`DittertRybin.uniform_maximum_four_rows` in
[FourRowFinal](../DR/Rectangular/FourRowFinal.lean) returns both orientations,
including the sharp bound and equality exactly at the uniform board.

The proof covers the whole integer range through three completed arguments:

- N=4 uses the [square order-four theorem](ORDER-FOUR-PROOF.md).
- 5≤N≤500 uses two exact polynomial certificate families, for the closed
  intervals [5,50] and [50,500]. The physical quintic identity, all 68
  strict small-block certificates, and all 20 full weighted kernels prove
  positivity and the constant kernel for every parameter in each interval.
- N≥500 uses the [analytic tail](FOUR-ROW-MINORANT.md), with the corrected
  endpoint minorant, actual contender concentration and strict column averaging.

The finite certificates use u=a/N with a=5 or 50 and 1/10≤u≤1.
All 680 Bernstein coefficient matrices and 2,760 positive Gram pivots are
checked exactly. Every full compressed row, including the omitted principal
coordinate, retains all degree-eight coefficients in the weighted kernel.
The ordinary multiplicities are 1, C, R and RC. The proof omits a standard
sector only when its ordinary index set makes that sector absent. Explicit
host permutations transfer the result to the actual cell matrices; positive
rescaling by 1/u preserves the PSD and constant-kernel conclusions.

The final tests cover N=4,5,50,500,501 and the transposed analytic range.
Both certificate families independently include N=50. Tests also retain
the exact 4×5 maximum 1071/4000, reject a smaller claimed constant, and
prove strict inequality whenever any cell is zero.

```
python3 scripts/generate_four_row_finite_kernel.py --check
python3 -O scripts/generate_four_row_finite_kernel.py --check
python3 scripts/generate_four_row_finite_diagonal_cache.py --check
python3 -O scripts/generate_four_row_finite_diagonal_cache.py --check
lake --wfail build +Test.FourRowFiniteCertifiedKernels +Test.FourRowFinal
```

See [the quintic bridge](FINITE-K4-QUINTIC-BRIDGE.md),
[source attribution](SOURCES.md) and [verification](VERIFICATION.md).
This scoped theorem does not settle arbitrary-rectangle P2. Independent
exact-commit CI and the complete release gate remain separate obligations.
