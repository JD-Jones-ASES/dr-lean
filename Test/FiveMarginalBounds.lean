import DR.Square.FiveMarginalBounds

/-! Exact controls for the noncircular stationary bootstrap and its closed boundary. -/

namespace DittertRybin.Tests

example : fiveDeficitParameter 0 = 0 := by simp [fiveDeficitParameter]
example : fiveRatioFloor < (601 / 625 : ℝ) ^ 2 := by norm_num [fiveRatioFloor]

-- Jumping directly from the initial envelope to the final negative slope fails.
example : (23 / 50 : ℝ) ^ 2 <
    8 / (25 * ((1 - (71 / 100) * (9 / 20)) * (1 + fiveRatioFloor))) := by
  norm_num [fiveRatioFloor]

-- The same invalid shortcut also fails for the positive slope.
example : (1 / 2 : ℝ) ^ 2 <
    2 * (1 + (71 / 100) * (9 / 20)) * (5 - (1 + (71 / 100) * (9 / 20))) /
      (25 * ((1 - (71 / 100) * (9 / 20)) * (1 + fiveRatioFloor))) := by
  norm_num [fiveRatioFloor]

-- The last step does not justify the stronger positive slope 49/100.
example : (49 / 100 : ℝ) ^ 2 <
    2 * (1 + (51 / 100) * (9 / 20)) * (5 - (1 + (51 / 100) * (9 / 20))) /
      (25 * ((1 - (47 / 100) * (9 / 20)) * (1 + fiveRatioFloor))) := by
  norm_num [fiveRatioFloor]

#print axioms log_deficit_ge_inverseVariance
#print axioms stationary_inverseVariance_coupled
#print axioms five_coordinate_inverseVariance_bound
#print axioms five_globalMax_inverseVariance_axis
#print axioms five_globalMax_marginal_bootstrap
#print axioms five_globalMax_marginal_bounds

end DittertRybin.Tests
