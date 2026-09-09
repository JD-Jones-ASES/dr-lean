import DR.Rectangular.ThreeRowMissingComparison

/-! Omitted row masses for proper supports, with arbitrary physical-column multiplicities. -/

namespace DittertRybin
open scoped BigOperators

/-- Every physical column has at least one actual zero. -/
def ThreeRowProperSupport {n : ℕ} (P : Board 3 n) : Prop := ∀ j, ∃ i, P i j = 0

private theorem fin_three_exhaustion (i h k l : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) :
    l = i ∨ l = h ∨ l = k := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> fin_cases l <;> simp_all

theorem threeRowDoublet_iff_other_rows {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (j : Fin n) :
    ThreeRowDoublet P i j ↔ P i j = 0 ∧ 0 < P h j ∧ 0 < P k j := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;>
    simp_all [ThreeRowDoublet, and_comm, and_left_comm]
  all_goals tauto

theorem ThreeRowProperSupport.zero_of_two_positive {n : ℕ} {P : Board 3 n}
    (hproper : ThreeRowProperSupport P) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (j : Fin n)
    (hh : 0 < P h j) (hk : 0 < P k j) : P i j = 0 := by
  obtain ⟨l, hl⟩ := hproper j
  rcases fin_three_exhaustion i h k l hih hik hhk with hi | hh' | hk'
  · simpa only [hi] using hl
  · exact False.elim ((ne_of_gt hh) (by simpa only [hh'] using hl))
  · exact False.elim ((ne_of_gt hk) (by simpa only [hk'] using hl))

/-- The row omitted by a doubleton has at least the mass of either occupied row.
All other columns may be nonidentical singletons or doubletons. -/
theorem IsSeparationGlobalMax.threeRow_proper_doublet_omitted_mass_ge {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hproper : ThreeRowProperSupport P) (h : Fin 3) (b : Fin n)
    (hw : ThreeRowDoublet P h b) (i : Fin 3) : rowSum P i ≤ rowSum P h := by
  by_cases hih : i = h
  · subst i
    exact le_rfl
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have hw' := (threeRowDoublet_iff_other_rows P h i k (Ne.symm hih) hkh.symm hki.symm b).mp hw
  by_contra hnot
  have hrow : rowSum P h < rowSum P i := lt_of_not_ge hnot
  have hterm (j : Fin n) : 0 ≤ P k j * (P i j + P i b - P h j) := by
    by_cases hkj : P k j = 0
    · rw [hkj, zero_mul]
    by_cases hhj : P h j = 0
    · rw [hhj, sub_zero]
      exact mul_nonneg (hP.1 k j) (add_nonneg (hP.1 i j) (hP.1 i b))
    have hkp : 0 < P k j := lt_of_le_of_ne (hP.1 k j) (Ne.symm hkj)
    have hhp : 0 < P h j := lt_of_le_of_ne (hP.1 h j) (Ne.symm hhj)
    have hz := hproper.zero_of_two_positive i h k hih hki.symm hkh.symm j hhp hkp
    have hvj : ThreeRowDoublet P i j :=
      (threeRowDoublet_iff_other_rows P i h k hih hki.symm hkh.symm j).mpr ⟨hz, hhp, hkp⟩
    have he := hmax.threeRow_doublet_exclusive_order hP hn i h hih j b hvj hw hrow
    apply mul_nonneg (hP.1 k j)
    linarith only [he, hP.1 i j]
  have hsum : 0 ≤ ∑ j ∈ Finset.univ.erase b, P k j * (P i j + P i b - P h j) :=
    Finset.sum_nonneg fun j _ => hterm j
  have hstrict := mul_pos (sub_pos.mpr hrow) hw'.2.2
  have hid := threeRow_missing_gradient_sum P i h k hih hki.symm hkh.symm b hw'.1
  have hgrad := hmax.threeRow_gradient_le hP (h, b) (i, b) hw'.2.1
  dsimp at hgrad
  linarith only [hsum, hstrict, hid, hgrad]

/-- Every two occurring doubleton types omit rows of exactly equal mass. -/
theorem IsSeparationGlobalMax.threeRow_proper_doublet_row_masses_eq {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hproper : ThreeRowProperSupport P) (i h : Fin 3) (a b : Fin n)
    (hv : ThreeRowDoublet P i a) (hw : ThreeRowDoublet P h b) : rowSum P i = rowSum P h :=
  le_antisymm (hmax.threeRow_proper_doublet_omitted_mass_ge hP hn hproper h b hw i)
    (hmax.threeRow_proper_doublet_omitted_mass_ge hP hn hproper i a hv h)

end DittertRybin
