import DR.Endpoint.PositiveMaximizers
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

private noncomputable def positiveTwo : Board 2 2 := !![3/8, 1/8; 1/8, 3/8]

private theorem positiveTwo_probability : IsProbability positiveTwo := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [positiveTwo]
  · norm_num [totalMass, rowSum, positiveTwo, Fin.sum_univ_succ]

private theorem positiveTwo_positive : ∀ i j, 0 < positiveTwo i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [positiveTwo]

-- A negative parameter increases the norm and remains in the actual simplex.
example : orderThreeSquareSum (blendColumns positiveTwo 0 1 (-1/4)) = 25/64 := by
  norm_num [orderThreeSquareSum, blendColumns, positiveTwo, Fin.sum_univ_succ]
example : IsProbability (blendColumns positiveTwo 0 1 (-1/4)) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [blendColumns, positiveTwo]
  · norm_num [totalMass, rowSum, blendColumns, positiveTwo, Fin.sum_univ_succ]
example : orderThreeSquareSum positiveTwo <
    orderThreeSquareSum (blendColumns positiveTwo 0 1 (-1/4)) := by
  norm_num [orderThreeSquareSum, blendColumns, positiveTwo, Fin.sum_univ_succ]
example : orderThreeSquareSum (blendColumns positiveTwo 0 1 (1/2)) = 1/4 := by
  norm_num [orderThreeSquareSum, blendColumns, positiveTwo, Fin.sum_univ_succ]
example : ∃ t : ℝ, t < 0 ∧ IsProbability (blendColumns positiveTwo 0 1 t) :=
  exists_negative_blend_probability positiveTwo_probability positiveTwo_positive 0 1 (by decide)

-- The signed identity includes empty row types and the swapping endpoint.
example (P : Board 0 2) (t : ℝ) :
    orderThreeSquareSum (blendColumns P 0 1 t) = orderThreeSquareSum P := by
  simp only [orderThreeSquareSum, Finset.univ_eq_empty, Finset.sum_empty]
example (P : Board 3 2) :
    orderThreeSquareSum (blendColumns P 0 1 1) = orderThreeSquareSum P := by
  rw [orderThreeSquareSum_blendColumns P 0 1 (by decide)]
  ring

-- Boundary points need not admit reverse averaging: positivity is used precisely here.
example (t : ℝ) (ht : t < 0) :
    ¬IsProbability (blendColumns (!![1, 0] : Board 1 2) 0 1 t) := by
  intro h
  have hentry := h.1 0 1
  norm_num [blendColumns] at hentry
  linarith

example : orderThreeSquareSum (uniformBoard 2 3) = 1/6 := by
  norm_num [orderThreeSquareSum_uniform (by decide : 0 < 2) (by decide : 0 < 3)]
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    orderThreeSquareSum P ≤ orderThreeSquareSum (uniformBoard m n) ↔ P = uniformBoard m n :=
  orderThreeSquareSum_le_uniform_iff hm hn ⟨hP, hmass⟩

-- The endpoint closure is instantiated with an independently proved order-two theorem.
example {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) : UniformMaximizer m n 2 := by
  apply uniform_maximizer_of_all_global_positive (by decide) hm hn
  intro P hP hmax
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hbound := uniform_maximum_order_two hm hn P hP
  have hcont := hmax _ (uniformBoard_isProbability hm0 hn0)
  rw [separationProbability_uniform hm0 hn0] at hcont
  have hPU := hbound.2.mp (le_antisymm hbound.1 hcont)
  subst P
  intro i j
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  simp only [uniformBoard]
  positivity

-- No positivity assumption is added to the board in the final sharp inequality.
example {m n k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) (hkn : k ≤ n)
    (hpositive : ∀ P : Board m n, IsProbability P →
      (∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k) →
      ∀ i j, 0 < P i j)
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P k ≤ uniformSeparationValue m n k ∧
      (separationProbability P k = uniformSeparationValue m n k ↔ P = uniformBoard m n) :=
  uniform_maximizer_of_all_global_positive hk hkm hkn hpositive P ⟨hP, hmass⟩

#print axioms orderThreeSquareSum_blendColumns
#print axioms exists_negative_blend_probability
#print axioms orderThreeSquareSum_le_uniform_iff
#print axioms exists_greatest_norm_globalMax
#print axioms greatest_norm_globalMax_columns_eq
#print axioms greatest_norm_globalMax_eq_uniform
#print axioms globalMax_eq_uniform_of_all_global_positive
#print axioms uniform_maximizer_of_all_global_positive

end DittertRybin.Tests
