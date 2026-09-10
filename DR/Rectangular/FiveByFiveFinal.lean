import DR.Rectangular.OrderTwo
import DR.Rectangular.OrderThreeFinal
import DR.Rectangular.FiveByFiveOrderFour
import DR.Square.SpectralFive

/-! All admissible nontrivial sample orders on the full 5-by-5 simplex. -/
namespace DittertRybin

theorem uniform_maximum_five_by_five {k : ℕ} (hk : 2≤k) (hk5 : k≤5) :
    UniformMaximizer 5 5 k := by
  interval_cases k
  · exact uniform_maximum_order_two (by decide) (by decide)
  · exact uniform_maximum_order_three (by decide) (by decide)
  · exact uniform_maximum_five_by_five_order_four
  · exact uniformMaximizer_five_five_five

end DittertRybin
