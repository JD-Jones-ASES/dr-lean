import DR.Rectangular.ThreeRowGradient
import DR.Rectangular.ThreeRowNoEmpty

/-! Exact comparison of two physical columns, with full-simplex conditions on their exclusive cells. -/

namespace DittertRybin
open scoped BigOperators

/-- The residual row mass after deleting two distinct physical columns. -/
def threeRowRemainingRow {n : ℕ} (P : Board 3 n) (a b : Fin n) (i : Fin 3) : ℝ :=
  rowSum P i - P i a - P i b

def threeRowColumnComparison {n : ℕ} (P : Board 3 n) (a b : Fin n) (i h : Fin 3) : ℝ :=
  if i = h then totalMass P - colSum P a - colSum P b
    else threeRowRemainingRow P a b i + threeRowRemainingRow P a b h

theorem rowSum_eraseColumns_pair {m n : ℕ} (P : Board m n) (a b : Fin n)
    (hab : a ≠ b) (i : Fin m) :
    rowSum (eraseColumns P {a, b}) i = rowSum P i - P i a - P i b := by
  have hterm (j : Fin n) : eraseColumns P {a, b} i j = P i j -
      (if j = a then P i a else 0) - (if j = b then P i b else 0) := by
    by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all [eraseColumns]
  simp only [rowSum, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem totalMass_eraseColumns_pair {m n : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) :
    totalMass (eraseColumns P {a, b}) = totalMass P - colSum P a - colSum P b := by
  simp only [totalMass, rowSum_eraseColumns_pair P a b hab, Finset.sum_sub_distrib, colSum]

theorem threeRowRemainingRow_nonneg {n : ℕ} {P : Board 3 n} (hP : ∀ i j, 0 ≤ P i j)
    (a b : Fin n) (hab : a ≠ b) (i : Fin 3) : 0 ≤ threeRowRemainingRow P a b i := by
  rw [threeRowRemainingRow, ← rowSum_eraseColumns_pair P a b hab]
  exact rowSum_nonneg (eraseColumns_nonneg hP {a, b}) i

/-- No sign assumptions are needed for this gradient comparison identity. -/
theorem threeRow_column_gradient_difference {n : ℕ} (P : Board 3 n)
    (a b : Fin n) (i : Fin 3) :
    threeRowReducedGradient P i a - threeRowReducedGradient P i b =
      -(∑ h, threeRowColumnComparison P a b i h * (P h a - P h b)) := by
  fin_cases i <;> simp [threeRowReducedGradient, threeRowColumnComparison, threeRowRemainingRow,
    totalMass, colSum, Fin.sum_univ_succ] <;> ring

/-- A positive donor in b imposes an inequality even if the corresponding a-entry is missing. -/
theorem IsSeparationGlobalMax.threeRow_comparison_nonneg {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (a b : Fin n) (i : Fin 3) (hib : 0 < P i b) :
    0 ≤ ∑ h, threeRowColumnComparison P a b i h * (P h a - P h b) := by
  have h := hmax.threeRow_gradient_le hP (i, a) (i, b) hib
  have hd := threeRow_column_gradient_difference P a b i
  dsimp at h
  linarith only [h, hd]

theorem IsSeparationGlobalMax.threeRow_comparison_eq_zero {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (a b : Fin n) (i : Fin 3) (hia : 0 < P i a) (hib : 0 < P i b) :
    (∑ h, threeRowColumnComparison P a b i h * (P h a - P h b)) = 0 := by
  have h := hmax.threeRow_gradient_eq hP (i, a) (i, b) hia hib
  have hd := threeRow_column_gradient_difference P a b i
  dsimp at h
  linarith only [h, hd]

/-- Deleting any physical pair leaves positive mass at a three-row global maximizer. -/
theorem IsSeparationGlobalMax.threeRow_remaining_mass_pos {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (a b : Fin n) (hab : a ≠ b) : 0 < totalMass P - colSum P a - colSum P b := by
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hcol := hmax.column_mass_pos hP hn c
  obtain ⟨i, _hi, hip⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hP.1 i c)).mp hcol
  have he := nonnegative_entry_le_totalMass (eraseColumns_nonneg hP.1 {a, b}) i c
  simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hca, hcb, or_self, if_false] at he
  rw [← totalMass_eraseColumns_pair P a b hab]
  exact hip.trans_le he

/-- A singleton column forces a positive opposite row-pair moment.
No assumption that all other columns are proper is needed. -/
theorem IsSeparationGlobalMax.threeRow_singleton_pair_pos {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i : Fin 3) (j : Fin n) (hp : 0 < P i j)
    (hzero1 : P (i + 1) j = 0) (hzero2 : P (i + 2) j = 0) : 0 < threeRowPair P i := by
  have hgrad := hmax.threeRow_gradient_le hP (i + 1, j) (i, j) hp
  have hd := threeRowReducedGradient_row_difference P i j
  rw [hzero1, hzero2] at hd
  have hr := hmax.row_mass_pos hP (by norm_num : 3 ≤ 3) (i + 2)
  have hJ := threeRowPair_nonneg hP.1 (i + 1)
  have hprod := mul_pos hr hp
  dsimp at hgrad
  nlinarith only [hgrad, hd, hJ, hprod]

end DittertRybin
