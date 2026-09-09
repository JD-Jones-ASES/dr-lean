import DR.Rectangular.OrderThreeLarge

namespace DittertRybin.Tests.OrderThreeLarge
open scoped BigOperators

-- A pure row direction has no residual, so the energy projection can be singular.
private noncomputable def rowDirection : Board 2 3 := fun i _ => if i = 0 then 1 / 3 else -1 / 3

example : totalMass rowDirection = 0 := by
  norm_num [totalMass, rowSum, rowDirection, Fin.sum_univ_two]

example : orderThreeResidual rowDirection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orderThreeResidual, rowSum, colSum, rowDirection, Fin.sum_univ_two]

example : orderThreeSquareSum rowDirection = 2 / 3 := by
  norm_num [orderThreeSquareSum, rowDirection, Fin.sum_univ_two]

example : orderThreeMarginalSquareSum rowDirection = 2 / 3 := by
  norm_num [orderThreeMarginalSquareSum, orderThreeRowSquareSum, orderThreeColSquareSum,
    rowSum, colSum, rowDirection, Fin.sum_univ_two]

-- A signed interaction direction has zero marginal energy and remains entirely in the residual.
private def interaction : Board 2 2 := fun i j => if i = j then 1 else -1

example : orderThreeMarginalSquareSum interaction = 0 := by
  norm_num [orderThreeMarginalSquareSum, orderThreeRowSquareSum, orderThreeColSquareSum,
    rowSum, colSum, interaction, Fin.sum_univ_two]

example : orderThreeResidual interaction = interaction := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orderThreeResidual, rowSum, colSum, interaction, Fin.sum_univ_two]

-- The tangent estimate retains its equality case at E=1, T=1/2.
example : -(3 / 4 * (1 : ℝ) + 3 / 2 * (1 / 2)) ≤ 6 * (-1 / 4) := by
  apply orderThree_mixed_tangent 1 (1 / 2) (1 / 2) (1 / 4) 2 (-1 / 4) <;> norm_num

-- Reducing the constant term destroys that exact equality control.
example : ¬ (-(7 / 10 * (1 : ℝ) + 3 / 2 * (1 / 2)) ≤ 6 * (-1 / 4)) := by norm_num

example : UniformMaximizer 10 10 3 := uniform_maximum_order_three_of_min_ge_ten (by norm_num) (by norm_num)
example : UniformMaximizer 238 6 3 := (uniform_maximum_order_three_six (by norm_num)).transpose
example : UniformMaximizer 7 25 3 := uniform_maximum_order_three_seven (by norm_num)
example : UniformMaximizer 8 15 3 := uniform_maximum_order_three_eight (by norm_num)
example : UniformMaximizer 9 12 3 := uniform_maximum_order_three_nine (by norm_num)

-- Every probability matrix with a zero cell is covered and is strictly suboptimal here.
example {P : Board 10 10} (hP : IsProbability P) (hz : P 0 0 = 0) :
    orderThreeFailurePolynomial (uniformBoard 10 10) < orderThreeFailurePolynomial P := by
  apply orderThreeFailurePolynomial_strict_of_criterion (by norm_num) (by norm_num)
    (orderThreeLargeDimensions_ge_ten (m := 10) (n := 10) (by norm_num) (by norm_num)).2 hP
  intro heq
  have hcell := congrFun (congrFun heq 0) 0
  rw [hz] at hcell
  norm_num [uniformBoard] at hcell

#print axioms DittertRybin.orderThreeFailurePolynomial_centered
#print axioms DittertRybin.orderThreeFailurePolynomial_far
#print axioms DittertRybin.orderThreeFailurePolynomial_near
#print axioms DittertRybin.uniform_maximum_order_three_of_min_ge_ten
#print axioms DittertRybin.uniform_maximum_order_three_six

end DittertRybin.Tests.OrderThreeLarge
