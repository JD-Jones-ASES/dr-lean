import DR.Square.SpectralFiveSetup

/-! The coarse floor has a positive margin throughout the closed certificate interval. -/
namespace DittertRybin.Tests

example : (79/100:ℝ) ≤ 1-(23/50)*(9/20) := by norm_num
example : ¬ ((4/5:ℝ) ≤ 1-(23/50)*(9/20)) := by norm_num

#print axioms five_globalMax_coarse_marginal_floor
#print axioms five_extremal_marginals_straddle_one
#print axioms five_globalMax_two_cut_contradiction

end DittertRybin.Tests
