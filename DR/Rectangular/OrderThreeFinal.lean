import DR.Rectangular.OrderThreeFinite4
import DR.Rectangular.OrderThreeFinite5
import DR.Rectangular.OrderThreeFinite6
import DR.Rectangular.OrderThreeFinite7
import DR.Rectangular.OrderThreeFinite8
import DR.Rectangular.OrderThreeFinite9
import DR.Rectangular.ThreeRowFinal
import DR.Rectangular.FourByFourThree
import DR.Rectangular.FourByFiveThree
import DR.Rectangular.OrderThreeFourRowFinal
import DR.Rectangular.OrderThreeLargeFive

/-! Complete K=3 on every rectangle with both sides at least three.
Every finite gap uses the literal checked certificate dispatcher; all
remaining dimensions use the proved infinite families. -/
namespace DittertRybin

private theorem uniform_maximum_order_three_ordered {m n : ℕ}
    (hm : 3 ≤ m) (hmn : m ≤ n) : UniformMaximizer m n 3 := by
  by_cases hlarge : 10 ≤ m
  · exact uniform_maximum_order_three_of_min_ge_ten hlarge (by omega)
  interval_cases m
  · exact uniformMaximizer_three_rows hmn
  · by_cases hn4 : n=4
    · subst n
      exact uniformMaximizer_four_by_four_three
    by_cases hn5 : n=5
    · subst n
      exact uniformMaximizer_four_by_five_three
    by_cases hfinite : n ≤ 959
    · exact uniformMaximizer_orderThree_finite_4 (by omega) hfinite
    exact uniformMaximizer_orderThree_four_rows (by omega)
  · by_cases hfinite : n ≤ 120
    · exact uniformMaximizer_orderThree_finite_5 hmn hfinite
    exact uniform_maximum_order_three_five (by omega)
  · by_cases hfinite : n ≤ 237
    · exact uniformMaximizer_orderThree_finite_6 hmn hfinite
    exact uniform_maximum_order_three_six (by omega)
  · by_cases hfinite : n ≤ 24
    · exact uniformMaximizer_orderThree_finite_7 hmn hfinite
    exact uniform_maximum_order_three_seven (by omega)
  · by_cases hfinite : n ≤ 14
    · exact uniformMaximizer_orderThree_finite_8 hmn hfinite
    exact uniform_maximum_order_three_eight (by omega)
  · by_cases hfinite : n ≤ 11
    · exact uniformMaximizer_orderThree_finite_9 hmn hfinite
    exact uniform_maximum_order_three_nine (by omega)

/-- Sharp closed-simplex inequality with uniform iff equality for every M,N>=3. -/
theorem uniform_maximum_order_three {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    UniformMaximizer m n 3 := by
  rcases le_total m n with hmn | hnm
  · exact uniform_maximum_order_three_ordered hm hmn
  · exact (uniform_maximum_order_three_ordered hn hnm).transpose

end DittertRybin
