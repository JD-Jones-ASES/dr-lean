# Fixed-board K=4 block certificates

The [two rational coefficient vectors](FINITE_K4_FIXED_SEEDS_SOURCE.md)
use the universal 407-role catalogue. `finiteK4FixedRoleLookup_key` checks the
balanced lookup on every literal key.

For each of ten multiplier triples on a board of order n=5 or n=20, let nr,nc
be the numbers of distinguished row and column labels. The ordinary counts
are R=n−nr and C=n−nc. The full trivial sector is indexed lexicographically
on (nr+1)×(nc+1) and has kernel weights 1,C,R,RC. Its principal block deletes
the final ordinary/ordinary coordinate. The remaining sectors are row-standard,
column-standard and scalar interaction. Each board has 40 strict blocks and
150 positive LDL pivots; the largest principal block is 15×15.

[FiniteK4FixedBlocks](../DR/Certificates/FiniteK4FixedBlocks.lean) defines the
matrices and proves their exact casts and reindexings. The algebra permits
signed entries and zero-count expressions; positivity transfer requires the
actual ordinary counts. Both fixed boards have R,C≥2 for every multiplier.

The [generator](../scripts/generate_finite_k4_fixed_blocks.py) computes exact
rational matrices and LDL factors. Lean checks the full weighted kernel and
each Gram identity. The [order-five](../DR/Certificates/FiniteK4FixedChecked5.lean)
and [order-twenty](../DR/Certificates/FiniteK4FixedChecked20.lean) interfaces
combine their ten cases. Their physical probability interpretations yield
[the 5×5 result](../DR/Rectangular/FiveByFiveOrderFour.lean) and
[the 20×20 result](../DR/Rectangular/TwentyByTwentyOrderFour.lean).

```sh
python3 scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 -O scripts/generate_finite_k4_fixed_blocks.py --all --check
python3 scripts/test_finite_k4_fixed_blocks.py
lake --wfail build +Test.FiniteK4FixedChecked5 +Test.FiniteK4FixedChecked20
```

The tests retain count-zero/count-one algebra, signed coefficients, strict
positivity for arbitrary nonzero real vectors, and the exact aggregate weights.
