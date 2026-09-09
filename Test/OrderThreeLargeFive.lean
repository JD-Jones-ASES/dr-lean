import DR.Rectangular.OrderThreeLargeFive

namespace DittertRybin.Tests.OrderThreeLargeFive
open scoped BigOperators

private def extremalRow : Fin 5 → ℝ := fun i => if i = 0 then 4 else -1

example : ∑ i, extremalRow i = 0 := by
  norm_num [extremalRow, Fin.sum_univ_succ]

-- The factor 4/5 is exact at a zero-sum row direction with one large coordinate.
example : extremalRow 0 ^ 2 = (4 / 5 : ℝ) * ∑ i, extremalRow i ^ 2 := by
  norm_num [extremalRow, Fin.sum_univ_succ]

example : extremalRow 0 ^ 2 ≤ ((5 : ℝ) - 1) / 5 * ∑ i, extremalRow i ^ 2 := by
  apply orderThree_zero_sum_coordinate_sq (by norm_num) extremalRow
  norm_num [extremalRow, Fin.sum_univ_succ]

-- Mutating the sharp row factor invalidates the bound.
example : ¬ (extremalRow 0 ^ 2 ≤ (3 / 4 : ℝ) * ∑ i, extremalRow i ^ 2) := by
  norm_num [extremalRow, Fin.sum_univ_succ]

-- The normalized direction retains both zero row energy and zero residual energy.
example : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 = 121 * 1 * u ^ 2 := by
  apply orderThree_row_energy_parameter <;> norm_num

example : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 121 = 121 * 1 * u ^ 2 := by
  apply orderThree_row_energy_parameter <;> norm_num

example : (27197 / 2772275 : ℝ) ≤ orderThreeFiveExpression 121 0 :=
  orderThreeFiveExpression_lower (by norm_num) (by norm_num) (by norm_num)

example : (27197 / 2772275 : ℝ) ≤ orderThreeFiveExpression 121 1 :=
  orderThreeFiveExpression_lower (by norm_num) (by norm_num) (by norm_num)

example : UniformMaximizer 5 121 3 := uniform_maximum_order_three_five (by norm_num)
example : UniformMaximizer 121 5 3 := (uniform_maximum_order_three_five (by norm_num)).transpose

example {n : ℕ} (hn : 121 ≤ n) : UniformMaximizer 5 n 3 :=
  uniform_maximum_order_three_five hn

-- The strict inequality also covers arbitrary boundary matrices with a zero cell.
example {P : Board 5 121} (hP : IsProbability P) (hz : P 0 0 = 0) :
    orderThreeFailurePolynomial (uniformBoard 5 121) < orderThreeFailurePolynomial P := by
  apply orderThreeFailurePolynomial_five_strict (by norm_num) hP
  intro heq
  have hcell := congrFun (congrFun heq 0) 0
  rw [hz] at hcell
  norm_num [uniformBoard] at hcell

#print axioms DittertRybin.orderThree_linear_upper_refined
#print axioms DittertRybin.orderThreeFailurePolynomial_five_prebound
#print axioms DittertRybin.orderThreeFiveExpression_lower
#print axioms DittertRybin.orderThreeFailurePolynomial_five_near
#print axioms DittertRybin.uniform_maximum_order_three_five

end DittertRybin.Tests.OrderThreeLargeFive
