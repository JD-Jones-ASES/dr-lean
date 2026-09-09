import DR.Collision.Averaging
import DR.Rectangular.OrderTwo
import DR.Rectangular.FourRowCorrection

/-!
# Exact second-order rook formulas for four-row averaging

All identities in this module hold for arbitrary real entries. They identify
the explicit row/cell-product kernel with the genuine rook-counting kernel.
-/

namespace DittertRybin

open scoped BigOperators

private theorem fourRow_injective_two_iff {α : Type*} (s : Fin 2 → α) :
    Function.Injective s ↔ s 0 ≠ s 1 := by
  constructor
  · intro hs he
    have h := hs he
    norm_num at h
  · intro hs i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Ordered distinct pairs are twice the elementary symmetric coefficient. -/
theorem fourRow_elementarySymmetric_two {n : ℕ} (p : Fin n → ℝ) :
    2 * elementarySymmetric p 2 = (∑ i, p i) ^ 2 - ∑ i, p i ^ 2 := by
  classical
  let e : {s : Fin 2 → Fin n // Function.Injective s} ≃ (Fin 2 ↪ Fin n) :=
    { toFun := fun s => ⟨s.val, s.property⟩
      invFun := fun s => ⟨s, s.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hi : eventMass p {s : Fin 2 → Fin n | Function.Injective s} =
      2 * elementarySymmetric p 2 := by
    rw [eventMass_eq_sum_subtype]
    calc
      _ = ∑ s : Fin 2 ↪ Fin n, ∏ t, p (s t) := by
        apply Fintype.sum_equiv e
        intro s
        rfl
      _ = _ := by rw [sum_embeddings_eq_factorial_elementary]; norm_num
  have hset : {s : Fin 2 → Fin n | s 0 = s 1}ᶜ =
      {s : Fin 2 → Fin n | Function.Injective s} := by
    ext s
    exact (fourRow_injective_two_iff s).symm
  have h := eventMass_add_compl p {s : Fin 2 → Fin n | s 0 = s 1}
  rw [hset, hi, eventMass_two_equal] at h
  linarith

/-- The two-sample functional is homogeneous before probability normalization. -/
theorem fourRow_separationProbability_two {m n : ℕ} (P : Board m n) :
    separationProbability P 2 = totalMass P ^ 2 - ∑ i, ∑ j, P i j ^ 2 := by
  have hset : {s : Fin 2 → Fin m × Fin n | s 0 = s 1}ᶜ =
      {s : Fin 2 → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s} := by
    ext s
    exact (separation_two_iff s).symm
  have h := eventMass_add_compl (fun a : Fin m × Fin n => P a.1 a.2)
    {s : Fin 2 → Fin m × Fin n | s 0 = s 1}
  rw [hset, eventMass_two_equal, sum_cell_weights, Fintype.sum_prod_type] at h
  change (∑ i, ∑ j, P i j ^ 2) + separationProbability P 2 = totalMass P ^ 2 at h
  linarith

/-- The exact two-rook count, with no sign or mass assumptions. -/
theorem fourRow_rookSum_two {m n : ℕ} (P : Board m n) :
    2 * rookSum P 2 = totalMass P ^ 2 - (∑ i, rowSum P i ^ 2) -
      (∑ j, colSum P j ^ 2) + ∑ i, ∑ j, P i j ^ 2 := by
  have hr := fourRow_elementarySymmetric_two (rowSum P)
  have hc := fourRow_elementarySymmetric_two (colSum P)
  rw [← totalMass_eq_sum_colSum] at hc
  change 2 * elementarySymmetric (rowSum P) 2 = totalMass P ^ 2 - _ at hr
  have h := separationProbability_eq_rook P 2
  rw [fourRow_separationProbability_two] at h
  norm_num at h
  linarith

/-- The remaining two rows contribute their row product minus their same-column inner product. -/
theorem fourRow_matchingExclusionKernel_two {n : ℕ} (T : Board 4 n) (i h : Fin 4) :
    matchingExclusionKernel T 2 i h = fourRowColumnComplement (rowSum T) i h -
      fourRowComplementCorrection T i h := by
  by_cases hih : i = h
  · simp [matchingExclusionKernel, fourRowColumnComplement, fourRowComplementCorrection, hih]
  have hr := fourRow_rookSum_two (eraseRows T {i,h})
  rw [matchingExclusionKernel, if_neg hih]
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hi : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hi i with rfl | rfl | rfl | rfl <;>
    rcases hi h with rfl | rfl | rfl | rfl
  all_goals try contradiction
  all_goals norm_num [fourRowColumnComplement, fourRowComplementCorrection, hu,
    Finset.prod_insert, Finset.erase_insert, Finset.erase_insert_of_ne,
    Finset.erase_singleton, Fin.ext_iff] at ⊢
  all_goals conv at hr =>
    rhs
    simp [totalMass, rowSum, colSum, Fin.sum_univ_four, eraseRows,
      add_sq, Finset.sum_add_distrib, ← Finset.mul_sum]
  all_goals simp only [mul_assoc, ← Finset.mul_sum] at hr
  all_goals simp only [rowSum]
  all_goals linarith

/-- The elementary column coefficient is exactly the half mass-square difference. -/
theorem fourRow_averagingCoefficient_two {n : ℕ} (T : Board 4 n) :
    averagingCoefficient T 2 = (totalMass T ^ 2 - fourRowColumnSquareMass T) / 2 := by
  have h := fourRow_elementarySymmetric_two (colSum T)
  rw [← totalMass_eq_sum_colSum] at h
  change 2 * averagingCoefficient T 2 = totalMass T ^ 2 - fourRowColumnSquareMass T at h
  linarith

/-- The explicit polynomial matrix is the actual order-two averaging kernel. -/
theorem fourRowBlendKernel_eq_averagingKernel {n : ℕ} (T : Board 4 n) :
    fourRowBlendKernel T = averagingKernel T 2 := by
  ext i h
  rw [averagingKernel, fourRow_averagingCoefficient_two, fourRow_matchingExclusionKernel_two]
  simp only [fourRowBlendKernel]
  ring

end DittertRybin
