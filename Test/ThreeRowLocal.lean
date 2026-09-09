import DR.Rectangular.ThreeRowLocal

/-! Exact local domain, normalization, orientation, and axiom controls. -/

open DittertRybin
open scoped BigOperators

example : ∃ ε : ℝ, 0 < ε ∧ ∀ P : Board 3 4,
    IsProbability P → P ≠ uniformBoard 3 4 →
    (∑ i, ∑ j, (P i j - 1 / 12) ^ 2) ≤ ε →
    separationProbability P 3 < separationProbability (uniformBoard 3 4) 3 := by
  obtain ⟨ε,hε,h⟩ := exists_strict_local_separation_uniform (by decide : 3 ≤ 3) (by decide : 3 ≤ 4)
  refine ⟨ε,hε,?_⟩
  intro P hP hPU hnear
  apply h P hP hPU
  convert hnear using 1
  norm_num [orderThreeSquareSum, orderThreeCentered, uniformBoard]

example : ∃ ε : ℝ, 0 < ε ∧ ∀ P : Board 7 3,
    IsProbability P → P ≠ uniformBoard 7 3 →
    orderThreeSquareSum (orderThreeCentered P) ≤ ε →
    separationProbability P 3 < separationProbability (uniformBoard 7 3) 3 :=
  exists_strict_local_separation_uniform (by decide) (by decide)

example (P : Board 3 3) (hP : IsProbability P)
    (hnear : orderThreeSquareSum (orderThreeCentered P) ≤ orderThreeLocalEnergyRadius 3 3) :
    (1 / 6 : ℝ) * orderThreeSquareSum (orderThreeCentered P) ≤
      separationProbability (uniformBoard 3 3) 3 - separationProbability P 3 := by
  have h := orderThreeFailurePolynomial_local_lower (by decide : 3 ≤ 3) (by decide : 3 ≤ 3) hP hnear
  norm_num [orderThreeLocalQuadraticCoefficient] at h
  have hPpoly := one_sub_separationProbability_three hP
  have hUpoly := one_sub_separationProbability_three
    (uniformBoard_isProbability (by decide : 0 < 3) (by decide : 0 < 3))
  linarith

example : orderThreeLocalQuadraticCoefficient 2 100 = 0 := by
  norm_num [orderThreeLocalQuadraticCoefficient]

example {m n : ℕ} (P : Board m n) :
    orderThreeSquareSum (orderThreeCentered P) = 0 ↔ P = uniformBoard m n :=
  (orderThreeSquareSum_eq_zero_iff _).trans (orderThreeCentered_eq_zero_iff P)

#print axioms DittertRybin.orderThree_mixed_lower_energy
#print axioms DittertRybin.orderThreeFailurePolynomial_local_lower
#print axioms DittertRybin.exists_strict_local_separation_uniform
