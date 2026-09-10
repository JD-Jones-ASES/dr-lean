# Complete P2 at three samples

[OrderThreeFinal.lean](../DR/Rectangular/OrderThreeFinal.lean) proves
`uniform_maximum_order_three`: for every m,n≥3, the uniform probability
matrix uniquely maximizes the probability that three iid samples have all
different rows or all different columns. The OR is inclusive. Every
nonnegative matrix of total mass one is included, with zero entries allowed.

The proof orders the two dimensions and joins these exact ranges:

| Smaller side | Finite part | Infinite part |
| --- | --- | --- |
| 3 | No gap | All n≥3 |
| 4 | Separate n=4,5; certificates n=6..959 | n≥960 |
| 5 | Certificates n=5..120 | n≥121 |
| 6 | Certificates n=6..237 | n≥238 |
| 7 | Certificates n=7..24 | n≥25 |
| 8 | Certificates n=8..14 | n≥15 |
| 9 | Certificates n=9..11 | n≥12 |
| At least 10 | No gap | All n at least the smaller side |

All 1,330 finite certificates and 87 exact dispatch shards have passed Lean.
Each certificate proves the literal polynomial equations and positive blocks
required by [the physical soundness theorem](FINITE-K3-BLOCK-SOUNDNESS.md).
Six finite-strip adapters cover exactly the listed integer intervals. The
[infinite components](ORDER-THREE-RANGES.md) and transposition finish every
rectangle. The [replay receipt](../data/FINITE_K3_COMPLETE_REPLAY.md) records
canonical coverage, generated-source reproduction and the trust audits.

Two additional required release results now follow:

- [SmallSideFinal.lean](../DR/Rectangular/SmallSideFinal.lean) combines K=2,
  complete K=3 and the four-row K=4 proof for every admissible
  2≤K≤min(m,n) when min(m,n)≤4.
- [FiveByFiveFinal.lean](../DR/Rectangular/FiveByFiveFinal.lean) combines
  K=2,3,4 and the square Dittert endpoint for every 2≤K≤5 on 5×5.

Both corollaries retain the actual sharp uniform probability and iff
equality on the full closed simplex. The K=1 nonuniqueness exception is
explicitly tested. These results do not settle P2 at arbitrary larger K.

Replay:

```sh
lake --wfail build +Test.OrderThreeFinal +Test.SmallSideFinal +Test.FiveByFiveFinal
```

Tests include 24 finite/infinite junctions in both orientations, arbitrary
boundary zeros, uniform attainment and rejected K=1 uniqueness. The final
and strip audits use only propext, Classical.choice and Quot.sound.
