import DR.Rectangular.ThreeRowProperPair

/-! Exact missing-cell comparison, without a census of column supports. -/

namespace DittertRybin
open scoped BigOperators

theorem threeRowPair_eq_other_rows {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) :
    threeRowPair P i = ∑ j, P h j * P k j := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> simp_all [threeRowPair, mul_comm]
  all_goals
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem threeRowReducedGradient_reindex {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (j : Fin n) :
    threeRowReducedGradient P i j = -colSum P j * (totalMass P - colSum P j) +
      threeRowPair P i + rowSum P h * P k j + rowSum P k * P h j - 2 * P h j * P k j := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> simp_all [threeRowReducedGradient] <;> ring

/-- A missing derivative is expressed as an actual sum over the other physical columns.
This algebraic identity permits signed entries and fully positive other columns. -/
theorem threeRow_missing_gradient_sum {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (b : Fin n) (hzero : P h b = 0) :
    threeRowReducedGradient P h b - threeRowReducedGradient P i b =
      (∑ j ∈ Finset.univ.erase b, P k j * (P i j + P i b - P h j)) +
        (rowSum P i - rowSum P h) * P k b := by
  have hfull : (∑ j, P k j * (P i j + P i b - P h j)) =
      threeRowPair P h - threeRowPair P i + rowSum P k * P i b := by
    rw [threeRowPair_eq_other_rows P h k i hhk hih.symm hik.symm,
      threeRowPair_eq_other_rows P i k h hik hih hhk.symm]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    unfold rowSum
    ring
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => P k j * (P i j + P i b - P h j)) (Finset.mem_univ b)
  rw [hfull, hzero] at herase
  rw [threeRowReducedGradient_reindex P h i k hih.symm hhk hik,
    threeRowReducedGradient_reindex P i h k hih hik hhk, hzero]
  nlinarith only [herase]

end DittertRybin
