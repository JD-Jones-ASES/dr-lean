import DR.Rectangular.ThreeRowKKT

/-! Exact cubic Hermite interpolation for actual three-sample probabilities. -/

namespace DittertRybin
open scoped BigOperators

private theorem sample_gradient_dot_three {α : Type*} [Fintype α] [DecidableEq α]
    (p D : α → ℝ) (s : Fin 3 → α) :
    (∑ a, sampleMassGradient p s a * D a) =
      D (s 0) * p (s 1) * p (s 2) + p (s 0) * D (s 1) * p (s 2) +
        p (s 0) * p (s 1) * D (s 2) := by
  rw [sampleMassGradient_dot, Fin.sum_univ_three]
  have h0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have h1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have h2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  rw [h0, h1, h2]
  simp only [Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2),
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1)]
  ring

/-- Repeated sample outcomes are allowed, and the weights may be signed. -/
theorem sampleMass_three_hermite {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) (s : Fin 3 → α) (t : ℝ) :
    sampleMass (fun a => (1 - t) * p a + t * q a) s =
      (1 - 3 * t ^ 2 + 2 * t ^ 3) * sampleMass p s +
      (3 * t ^ 2 - 2 * t ^ 3) * sampleMass q s +
      (t - 2 * t ^ 2 + t ^ 3) * (∑ a, sampleMassGradient p s a * (q a - p a)) +
      (-t ^ 2 + t ^ 3) * (∑ a, sampleMassGradient q s a * (q a - p a)) := by
  rw [sample_gradient_dot_three, sample_gradient_dot_three]
  simp only [sampleMass, Fin.prod_univ_three]
  ring

/-- The value and endpoint derivatives determine the full actual event polynomial. -/
theorem eventMass_three_hermite {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) (E : Set (Fin 3 → α)) (t : ℝ) :
    eventMass (fun a => (1 - t) * p a + t * q a) E =
      (1 - 3 * t ^ 2 + 2 * t ^ 3) * eventMass p E +
      (3 * t ^ 2 - 2 * t ^ 3) * eventMass q E +
      (t - 2 * t ^ 2 + t ^ 3) * (∑ a, eventMassGradient p E a * (q a - p a)) +
      (-t ^ 2 + t ^ 3) * (∑ a, eventMassGradient q E a * (q a - p a)) := by
  classical
  have hdot (p' : α → ℝ) : (∑ a, eventMassGradient p' E a * (q a - p a)) =
      ∑ s, if s ∈ E then ∑ a, sampleMassGradient p' s a * (q a - p a) else 0 := by
    simp only [eventMassGradient, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ E <;> simp only [hs, if_true, if_false, Finset.sum_const_zero]
  rw [hdot p, hdot q]
  unfold eventMass
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ E
  · simpa only [if_pos hs] using sampleMass_three_hermite p q s t
  · simp only [if_neg hs, mul_zero, add_zero]

/-- Cubic interpolation for the inclusive-OR functional on any finite rectangle. -/
theorem separationProbability_three_hermite {m n : ℕ} (P Q : Board m n) (t : ℝ) :
    separationProbability (fun i j => (1 - t) * P i j + t * Q i j) 3 =
      (1 - 3 * t ^ 2 + 2 * t ^ 3) * separationProbability P 3 +
      (3 * t ^ 2 - 2 * t ^ 3) * separationProbability Q 3 +
      (t - 2 * t ^ 2 + t ^ 3) * (∑ i, ∑ j, separationGradient P 3 i j * (Q i j - P i j)) +
      (-t ^ 2 + t ^ 3) * (∑ i, ∑ j, separationGradient Q 3 i j * (Q i j - P i j)) := by
  simpa only [separationProbability, separationGradient, Fintype.sum_prod_type] using
    eventMass_three_hermite (fun a : Fin m × Fin n => P a.1 a.2)
      (fun a : Fin m × Fin n => Q a.1 a.2)
      {s : Fin 3 → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s} t

end DittertRybin
