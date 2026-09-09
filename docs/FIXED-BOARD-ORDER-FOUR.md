# Four samples on the 5×5 and 20×20 boards

Both theorems concern every nonnegative real probability matrix, including
zero cells. Their exact sharp values are:

| Board | Uniform success probability | Equality |
|---|---|---|
| 5×5 | 5424/15625 | Exactly the uniform board |
| 20×20 | 14805351/16000000 | Exactly the uniform board |

The public declarations are
`DittertRybin.uniform_maximum_five_by_five_order_four` in
[FiveByFiveOrderFour](../DR/Rectangular/FiveByFiveOrderFour.lean) and
`DittertRybin.uniform_maximum_twenty_by_twenty_order_four` in
[TwentyByTwentyOrderFour](../DR/Rectangular/TwentyByTwentyOrderFour.lean).
These are two of the required release targets. They do not prove the full
arbitrary-rectangle P2 conjecture.

## Mathematical argument

The [quintic probability identity](FINITE-K4-QUINTIC-BRIDGE.md) expresses
the sharp deficit, multiplied by total mass, as a weighted sum of quadratic
forms indexed by triples of cells. The identity is exact on signed boards
and uses all 91 coefficient equations. Nonnegativity enters when applying
the identity to a probability board.

Every triple is carried to one of ten canonical seeds by actual row and
column permutations. For each seed, distinguish its occupied rows and
columns from the ordinary rows and columns. The compressed full matrix has
the multiplicity vector with entries 1, C, R and RC, where R and C are the
actual numbers of ordinary rows and columns. Its checked null vector is
this weighted vector. The all-one compressed vector generally is not null.

An exact strict Gram certificate for the principal block, together with the
full weighted kernel, proves that the compressed matrix is positive
semidefinite and its kernel is precisely that weighted span. Strict Gram
certificates for the row, column and interaction sectors then give
positivity of the actual physical matrix and exactly its constant kernel.
Both host dimensions are at least five, so every required sector is present.
The [generic soundness theorem](../DR/Certificates/FiniteK4FixedSoundness.lean)
transports these conclusions to all physical triples. The quintic identity
gives the sharp bound, and its repeated-cell terms force constant entries
in the equality case. Total mass fixes the uniform value.

Across both boards, Lean checks 20 full weighted kernels, 80 strict blocks
and 300 positive pivots. The largest principal block has size 15×15.
Exact rational generation is only a source of certificates: the compiled
identities and proved real-matrix soundness supply the mathematical evidence.
The [source note](../data/FINITE_K4_FIXED_BLOCKS_SOURCE.md) records generation
and provenance; see [attribution](SOURCES.md) for the Lab research context.

## Verification

The tests retain signed coefficients and zero ordinary counts for the cast
identity, reject the unweighted kernel, and prove strict inequality for
every probability board with a zero cell. The uniform board attains each
displayed constant, and lowering its numerator by one fails.

```
python3 scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 -O scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 scripts/test_finite_k4_fixed_blocks.py
python3 -O scripts/test_finite_k4_fixed_blocks.py
lake --wfail build +Test.FiniteK4FixedChecked5 +Test.FiniteK4FixedChecked20
lake --wfail build +Test.FiveByFiveOrderFour +Test.TwentyByTwentyOrderFour
```

For a cold checkout use the bounded dependency builder in
[verification](VERIFICATION.md). Local completion is separate from exact-commit
independent CI and the full public-release gate.
