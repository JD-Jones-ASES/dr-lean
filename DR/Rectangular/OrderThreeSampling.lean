import DR.Rectangular.OrderThreePolynomial
import DR.Collision.FirstMoment

/-!
# The exact three-sample failure polynomial

Repeated cells and the six ordered L-shaped configurations are counted
pointwise. Summing this identity gives the homogeneous cubic on every real
board; normalization to a probability matrix is a separate final step.
-/

namespace DittertRybin
open scoped BigOperators
open Classical

private def tripleSymmetrySum {α : Type*} (f : α → α → α → ℝ) (a b c : α) : ℝ :=
  f a b c + f a c b + f b a c + f b c a + f c a b + f c b a

private theorem sum_tripleSymmetrySum {α : Type*} [Fintype α] (f : α → α → α → ℝ) :
    (∑ a, ∑ b, ∑ c, tripleSymmetrySum f a b c) = 6 * ∑ a, ∑ b, ∑ c, f a b c := by
  have h12 (g : α → α → α → ℝ) : (∑ a, ∑ b, ∑ c, g b a c) = ∑ a, ∑ b, ∑ c, g a b c :=
    Finset.sum_comm
  have h23 (g : α → α → α → ℝ) : (∑ a, ∑ b, ∑ c, g a c b) = ∑ a, ∑ b, ∑ c, g a b c :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have h231 : (∑ a, ∑ b, ∑ c, f b c a) = ∑ a, ∑ b, ∑ c, f a b c :=
    (h12 (fun a b c => f a c b)).trans (h23 f)
  have h312 : (∑ a, ∑ b, ∑ c, f c a b) = ∑ a, ∑ b, ∑ c, f a b c :=
    (h23 (fun a b c => f b a c)).trans (h12 f)
  have h321 : (∑ a, ∑ b, ∑ c, f c b a) = ∑ a, ∑ b, ∑ c, f a b c :=
    (h12 (fun a b c => f c a b)).trans h312
  simp only [tripleSymmetrySum, Finset.sum_add_distrib]
  rw [h23 f, h12 f, h231, h312, h321]
  ring

private theorem injective_three_iff {α : Type*} (f : Fin 3 → α) :
    Function.Injective f ↔ f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide), h.ne (by decide), h.ne (by decide)⟩
  · rintro ⟨h01, h02, h12⟩ i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- A finite equality-pattern calculation, independent of the cell weights. -/
private theorem failure_three_indicator {m n : ℕ} (P : Board m n)
    (a b c : Fin m × Fin n) :
    (if ¬ (RowsDistinct ![a,b,c] ∨ ColsDistinct ![a,b,c]) then
        P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
      (1/2 : ℝ) * tripleSymmetrySum
        (fun a b c => if a = b then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) a b c +
      tripleSymmetrySum
        (fun a b c => if a.1 = b.1 ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) a b c -
      tripleSymmetrySum
        (fun a b c => if a = b ∧ a.1 = c.1 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) a b c -
      tripleSymmetrySum
        (fun a b c => if a = b ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) a b c +
      4 * (if a = b ∧ a = c then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) := by
  classical
  simp only [RowsDistinct, ColsDistinct, injective_three_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_cases hr01 : a.1 = b.1 <;> by_cases hr02 : a.1 = c.1 <;>
    by_cases hr12 : b.1 = c.1 <;> by_cases hc01 : a.2 = b.2 <;>
    by_cases hc02 : a.2 = c.2 <;> by_cases hc12 : b.2 = c.2 <;>
    simp_all [tripleSymmetrySum, Prod.ext_iff, eq_comm]
  all_goals first | (apply Or.inl; ring) | ring

private theorem sum_equal_pair_three {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    (∑ a, ∑ b, ∑ c, if a = b then p a * p b * p c else 0) =
      (∑ a, p a ^ 2) * (∑ c, p c) := by
  have ht (a b c : α) : (if a = b then p a * p b * p c else 0) =
      (if a = b then p a * p b else 0) * p c := by
    by_cases h : a = b <;> simp [h]
  simp_rw [ht, ← Finset.mul_sum]
  simp [← Finset.sum_mul, pow_two]

private theorem sum_equal_pair_row_three {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n, ∑ c : Fin m × Fin n,
      if a = b ∧ a.1 = c.1 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
        ∑ a : Fin m × Fin n, P a.1 a.2 ^ 2 * rowSum P a.1 := by
  have ht (a b c : Fin m × Fin n) :
      (if a = b ∧ a.1 = c.1 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
      (if a = b then P a.1 a.2 * P b.1 b.2 else 0) *
        (if a.1 = c.1 then P c.1 c.2 else 0) := by
    by_cases h : a = b <;> by_cases hr : a.1 = c.1 <;> simp [h, hr]
  simp_rw [ht, ← Finset.mul_sum, sum_row_eq_weight]
  simp [pow_two]

private theorem sum_equal_pair_col_three {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n, ∑ c : Fin m × Fin n,
      if a = b ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
        ∑ a : Fin m × Fin n, P a.1 a.2 ^ 2 * colSum P a.2 := by
  have ht (a b c : Fin m × Fin n) :
      (if a = b ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
      (if a = b then P a.1 a.2 * P b.1 b.2 else 0) *
        (if a.2 = c.2 then P c.1 c.2 else 0) := by
    by_cases h : a = b <;> by_cases hr : a.2 = c.2 <;> simp [h, hr]
  simp_rw [ht, ← Finset.mul_sum, sum_col_eq_weight]
  simp [pow_two]

private theorem sum_all_equal_three {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    (∑ a, ∑ b, ∑ c, if a = b ∧ a = c then p a * p b * p c else 0) =
      ∑ a, p a ^ 3 := by
  simp [ite_and, pow_succ]

private def sampleThreeEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun s := (s 0, s 1, s 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

private theorem sum_sample_three {α : Type*} [Fintype α] (f : (Fin 3 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, f ![a,b,c] := by
  rw [← (sampleThreeEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem sum_overlap_three {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n, ∑ c : Fin m × Fin n,
      if a.1 = b.1 ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
        mixedCollisionMoment P := by
  have h := overlapping_pattern_mass P
  unfold eventMass at h
  rw [sum_sample_three] at h
  simpa only [sampleMass, Fin.prod_univ_three, Set.mem_ofPred_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

private theorem sum_equal_pair_three_board {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n, ∑ c : Fin m × Fin n,
      if a = b then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
      cellSquareSum P * totalMass P := by
  simpa only [cellSquareSum, sum_cell_weights] using
    sum_equal_pair_three (fun a : Fin m × Fin n => P a.1 a.2)

private theorem sum_all_equal_three_board {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n, ∑ c : Fin m × Fin n,
      if a = b ∧ a = c then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
      ∑ a : Fin m × Fin n, P a.1 a.2 ^ 3 :=
  sum_all_equal_three (fun a : Fin m × Fin n => P a.1 a.2)

/-- The exact failure-event mass on arbitrary signed boards, with no normalization premise. -/
theorem eventMass_failure_three {m n : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin 3 → Fin m × Fin n | ¬ (RowsDistinct s ∨ ColsDistinct s)} =
      orderThreeFailurePolynomial P := by
  unfold eventMass
  rw [sum_sample_three]
  simp only [sampleMass, Fin.prod_univ_three, Set.mem_ofPred_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [failure_three_indicator]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_tripleSymmetrySum, sum_tripleSymmetrySum, sum_tripleSymmetrySum,
    sum_tripleSymmetrySum]
  rw [sum_equal_pair_three_board P, sum_overlap_three P,
    sum_equal_pair_row_three P, sum_equal_pair_col_three P,
    sum_all_equal_three_board P]
  simp only [cellSquareSum, mixedCollisionMoment, Fintype.sum_prod_type, orderThreeFailurePolynomial,
    mul_add, Finset.sum_add_distrib]
  ring

/-- The original sampling probability is the total cubic mass minus the failure polynomial. -/
theorem separationProbability_three_homogeneous {m n : ℕ} (P : Board m n) :
    separationProbability P 3 = totalMass P ^ 3 - orderThreeFailurePolynomial P := by
  have h := eventMass_add_compl (fun a : Fin m × Fin n => P a.1 a.2)
    {s : Fin 3 → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s}
  change separationProbability P 3 + eventMass (fun a : Fin m × Fin n => P a.1 a.2)
    {s : Fin 3 → Fin m × Fin n | ¬ (RowsDistinct s ∨ ColsDistinct s)} = _ at h
  rw [eventMass_failure_three, sum_cell_weights] at h
  linarith

/-- On the full probability simplex, the polynomial is exactly the failure probability. -/
theorem one_sub_separationProbability_three {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) : 1 - separationProbability P 3 = orderThreeFailurePolynomial P := by
  rw [separationProbability_three_homogeneous, hP.2]
  ring

end DittertRybin
