import DR.Rectangular.OrderThreeLargeDimensions

open DittertRybin

example : orderThreeLargeCriterion 10 10 = 43/1100 := by
  norm_num [orderThreeLargeCriterion]
example : orderThreeLargeCriterion 6 238 = 1/7140 := by
  norm_num [orderThreeLargeCriterion]
example : orderThreeLargeCriterion 7 25 = 31/1820 := by
  norm_num [orderThreeLargeCriterion]
example : orderThreeLargeCriterion 8 15 = 1/60 := by
  norm_num [orderThreeLargeCriterion]
example : orderThreeLargeCriterion 9 12 = 107/2052 := by
  norm_num [orderThreeLargeCriterion]

/-- This particular analytic criterion does not cover the adjacent omitted endpoint. -/
example : orderThreeLargeCriterion 6 237 < 0 := by norm_num [orderThreeLargeCriterion]
example : orderThreeLargeCriterion 9 9 < 0 := by norm_num [orderThreeLargeCriterion]

#print axioms DittertRybin.orderThreeLargeDimensions_ge_ten
#print axioms DittertRybin.orderThreeLargeDimensions_of_endpoint
