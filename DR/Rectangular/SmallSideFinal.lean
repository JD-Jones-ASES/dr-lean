import DR.Rectangular.OrderThreeFinal
import DR.Rectangular.FourRowFinal
import DR.Rectangular.OrderTwo

/-! Every admissible sample order when the smaller side is two, three or four.
The order guards retain the separate K=1 nonuniqueness case. -/
namespace DittertRybin

theorem uniform_maximum_small_side {m n k : ℕ}
    (hsmall : min m n≤4) (hk : 2≤k) (hkmn : k≤min m n) : UniformMaximizer m n k := by
  have hkm : k≤m := hkmn.trans (Nat.min_le_left m n)
  have hkn : k≤n := hkmn.trans (Nat.min_le_right m n)
  rcases (show k=2 ∨ k=3 ∨ k=4 by omega) with h | h | h
  · subst k
    exact uniform_maximum_order_two hkm hkn
  · subst k
    exact uniform_maximum_order_three hkm hkn
  · subst k
    rcases (show m=4 ∨ n=4 by omega) with hm | hn
    · subst m
      exact (uniform_maximum_four_rows hkn).1
    · subst n
      exact (uniform_maximum_four_rows hkm).2

end DittertRybin
