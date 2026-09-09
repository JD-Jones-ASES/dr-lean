import DR.Rectangular.ThreeRowFullPairs

/-! Strict reverse ordering of equal full columns, derived from actual missing-cell gradients. -/

namespace DittertRybin
open scoped BigOperators

/-- Only the fully positive physical columns are required to coincide. -/
def ThreeRowFullColumnsEqual {n : ℕ} (P : Board 3 n) : Prop :=
  ∀ a b, ThreeRowFullColumn P a → ThreeRowFullColumn P b → ∀ i, P i a = P i b

private theorem fin_three_exhaustion_full (i h k r : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) : r = i ∨ r = h ∨ r = k := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> fin_cases r <;> simp_all

theorem threeRow_full_column_of_three {n : ℕ} {P : Board 3 n} (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (a : Fin n)
    (hi : 0 < P i a) (hh : 0 < P h a) (hk : 0 < P k a) : ThreeRowFullColumn P a := by
  intro r
  rcases fin_three_exhaustion_full i h k r hih hik hhk with hr | hr | hr
  · simpa only [hr] using hi
  · simpa only [hr] using hh
  · simpa only [hr] using hk

/-- The full-column entries reverse the row-mass order with a strict doubleton-entry offset.
All other proper columns may be nonidentical and have arbitrary multiplicities. -/
theorem IsSeparationGlobalMax.threeRow_full_column_offset {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hsame : ThreeRowFullColumnsEqual P) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (b : Fin n) (hb : ThreeRowDoublet P h b) (q : Fin n) (hq : ThreeRowFullColumn P q)
    (hrow : rowSum P h < rowSum P i) : P i q + P i b < P h q := by
  have hb' := (threeRowDoublet_iff_other_rows P h i k hih.symm hhk hik b).mp hb
  by_contra hnot
  have hcoef : 0 ≤ P i q + P i b - P h q := sub_nonneg.mpr (le_of_not_gt hnot)
  have hterm (j : Fin n) : 0 ≤ P k j * (P i j + P i b - P h j) := by
    by_cases hk0 : P k j = 0
    · rw [hk0, zero_mul]
    have hkp : 0 < P k j := lt_of_le_of_ne (hP.1 k j) (Ne.symm hk0)
    apply mul_nonneg (hP.1 k j)
    by_cases hh0 : P h j = 0
    · rw [hh0, sub_zero]
      exact add_nonneg (hP.1 i j) (hP.1 i b)
    have hhp : 0 < P h j := lt_of_le_of_ne (hP.1 h j) (Ne.symm hh0)
    by_cases hi0 : P i j = 0
    · have hd : ThreeRowDoublet P i j :=
        (threeRowDoublet_iff_other_rows P i h k hih hik hhk j).mpr ⟨hi0, hhp, hkp⟩
      have he := hmax.threeRow_doublet_exclusive_order hP hn i h hih j b hd hb hrow
      rw [hi0, zero_add]
      exact sub_nonneg.mpr he
    · have hip : 0 < P i j := lt_of_le_of_ne (hP.1 i j) (Ne.symm hi0)
      have hf := threeRow_full_column_of_three i h k hih hik hhk j hip hhp hkp
      rw [hsame j q hf hq i, hsame j q hf hq h]
      exact hcoef
  have hsum : 0 ≤ ∑ j ∈ Finset.univ.erase b, P k j * (P i j + P i b - P h j) :=
    Finset.sum_nonneg fun j _ => hterm j
  have hstrict := mul_pos (sub_pos.mpr hrow) hb'.2.2
  have hid := threeRow_missing_gradient_sum P i h k hih hik hhk b hb'.1
  have hgrad := hmax.threeRow_gradient_le hP (h, b) (i, b) hb'.2.1
  dsimp at hgrad
  linarith only [hsum, hstrict, hid, hgrad]

/-- Support floors retain the exact doubleton, including its missing cell. -/
theorem SameSupportFloor.threeRowDoublet {n : ℕ} {P Q : Board 3 n} {ε : ℝ}
    (hfloor : SameSupportFloor P ε Q) (hε : 0 < ε) {i : Fin 3} {a : Fin n}
    (ha : ThreeRowDoublet P i a) : ThreeRowDoublet Q i a := by
  refine ⟨(hfloor i a).1 ha.1, ?_, ?_⟩
  · exact hε.trans_le ((hfloor (i + 1) a).2 ha.2.1)
  · exact hε.trans_le ((hfloor (i + 2) a).2 ha.2.2)

theorem SameSupportFloor.threeRowFullColumn {n : ℕ} {P Q : Board 3 n} {ε : ℝ}
    (hfloor : SameSupportFloor P ε Q) (hε : 0 < ε) {a : Fin n}
    (ha : ThreeRowFullColumn P a) : ThreeRowFullColumn Q a :=
  fun i => hε.trans_le ((hfloor i a).2 (ha i))

/-- The compact support normal form makes every full column identical at one actual global maximum. -/
theorem exists_threeRow_full_equal_normal_form {n : ℕ} {P : Board 3 n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3) :
    ∃ (ε : ℝ) (Q : Board 3 n), 0 < ε ∧ IsProbability Q ∧ IsSeparationGlobalMax Q 3 ∧
      SameSupportFloor P ε Q ∧ ThreeRowFullColumnsEqual Q := by
  obtain ⟨ε, Q, hε, hQ, hQmax, hfloor, hcols, _hrows⟩ :=
    exists_same_support_normal_form hP hmax (by norm_num : 2 ≤ 3)
  refine ⟨ε, Q, hε, hQ, hQmax, hfloor, ?_⟩
  intro a b ha hb
  apply hcols a b
  intro i
  exact iff_of_true ((hfloor.support_iff hP.1 hε i a).mp (ha i))
    ((hfloor.support_iff hP.1 hε i b).mp (hb i))

end DittertRybin
