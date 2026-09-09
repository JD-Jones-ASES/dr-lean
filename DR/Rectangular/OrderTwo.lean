import DR.Uniform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The complete two-sample rectangular theorem

For two samples, simultaneous row and column collision means that the two
sampled cells are identical. Its exact probability is the sum of squared
cell weights. The deficit from uniform is therefore exactly the squared
Euclidean distance from the uniform board. This proves both optimality and
uniqueness on every nonempty rectangle, including its boundary supports.
-/

namespace DittertRybin

open scoped BigOperators

private theorem injective_fin_two_iff {α : Type*} (f : Fin 2 → α) :
    Function.Injective f ↔ f 0 ≠ f 1 := by
  constructor
  · intro hf he
    have h := hf he
    norm_num at h
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Two sampled cells form a semimatching exactly when they are different. -/
theorem separation_two_iff {m n : ℕ} (s : Fin 2 → Fin m × Fin n) :
    RowsDistinct s ∨ ColsDistinct s ↔ s 0 ≠ s 1 := by
  rw [RowsDistinct, ColsDistinct, injective_fin_two_iff, injective_fin_two_iff]
  exact not_and_or.symm.trans (not_congr Prod.ext_iff.symm)

/-- The mass of the identical-outcome event for two independent samples. -/
theorem eventMass_two_equal {α : Type*} [Fintype α] (p : α → ℝ) :
    eventMass p {s : Fin 2 → α | s 0 = s 1} = ∑ a, p a ^ 2 := by
  classical
  unfold eventMass
  calc
    (∑ s : Fin 2 → α, if s ∈ {s | s 0 = s 1} then sampleMass p s else 0) =
        ∑ ab : α × α, if ab.1 = ab.2 then p ab.1 * p ab.2 else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv α)
      intro s
      by_cases hs : s 0 = s 1 <;>
        simp [sampleMass, Fin.prod_univ_two, finTwoArrowEquiv, piFinTwoEquiv, hs]
    _ = _ := by simp [Fintype.sum_prod_type, pow_two]

/-- The exact two-sample functional, on the entire probability simplex. -/
theorem separationProbability_two {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) :
    separationProbability P 2 = 1 - ∑ a : Fin m × Fin n, P a.1 a.2 ^ 2 := by
  have he : {s : Fin 2 → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s} =
      {s : Fin 2 → Fin m × Fin n | s 0 = s 1}ᶜ := by
    ext s
    exact separation_two_iff s
  unfold separationProbability
  rw [he, eventMass_compl _ ((sum_cell_weights P).trans hP.2), eventMass_two_equal]

/-- The exact second-moment identity around the uniform board. -/
theorem sum_sq_sub_uniformBoard {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    (∑ a : Fin m × Fin n, (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2) =
      (∑ a : Fin m × Fin n, P a.1 a.2 ^ 2) - ((m : ℝ) * n)⁻¹ := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (sum_cell_weights P).trans hP.2
  simp only [uniformBoard, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  field_simp
  ring

/-- The uniform two-sample probability has an exact squared-distance deficit. -/
theorem separationProbability_two_deficit {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    separationProbability (uniformBoard m n) 2 - separationProbability P 2 =
      ∑ a : Fin m × Fin n, (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [separationProbability_two (uniformBoard_isProbability hm hn),
    separationProbability_two hP, sum_sq_sub_uniformBoard hm hn hP]
  simp only [uniformBoard, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  field_simp
  ring

/-- Uniformity is the unique two-sample maximizer on every nonempty rectangle. -/
theorem uniform_maximum_order_two_of_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    UniformMaximizer m n 2 := by
  intro P hP
  have hdef := separationProbability_two_deficit hm hn hP
  have hu := separationProbability_uniform (k := 2) hm hn
  have hs : 0 ≤ ∑ a : Fin m × Fin n,
      (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  constructor
  · linarith
  · constructor
    · intro h
      have hz : (∑ a : Fin m × Fin n,
          (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2) = 0 := by linarith
      have heach := (Finset.sum_eq_zero_iff_of_nonneg
        (fun (a : Fin m × Fin n) (_ : a ∈ Finset.univ) ↦
          sq_nonneg (P a.1 a.2 - uniformBoard m n a.1 a.2))).mp hz
      ext i j
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (heach (i, j) (Finset.mem_univ _)))
    · intro h
      rw [h, hu]

/-- Rybin P2 for sample order two, on every admissible rectangle. -/
theorem uniform_maximum_order_two {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    UniformMaximizer m n 2 :=
  uniform_maximum_order_two_of_pos (by omega) (by omega)

end DittertRybin
