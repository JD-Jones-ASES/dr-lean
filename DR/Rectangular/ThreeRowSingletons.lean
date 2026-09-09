import DR.Rectangular.ThreeRowProperMasses

/-! Support exclusions involving singleton columns, with other columns unrestricted. -/

namespace DittertRybin
open scoped BigOperators

/-- A singleton records both actual zeros and the strict positivity of its one entry. -/
def ThreeRowSingleton {n : ℕ} (P : Board 3 n) (i : Fin 3) (j : Fin n) : Prop :=
  0 < P i j ∧ P (i + 1) j = 0 ∧ P (i + 2) j = 0

theorem threeRowSingleton_iff_other_rows {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (j : Fin n) :
    ThreeRowSingleton P i j ↔ 0 < P i j ∧ P h j = 0 ∧ P k j = 0 := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;>
    simp_all [ThreeRowSingleton, and_comm, and_left_comm]
  all_goals tauto

/-- Exact missing-versus-positive derivative at a singleton column. -/
theorem threeRow_singleton_gradient_difference {n : ℕ} (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (j : Fin n)
    (hhzero : P h j = 0) (hkzero : P k j = 0) :
    threeRowReducedGradient P h j - threeRowReducedGradient P i j =
      threeRowPair P h - threeRowPair P i + rowSum P k * P i j := by
  rw [threeRowReducedGradient_reindex P h i k hih.symm hhk hik,
    threeRowReducedGradient_reindex P i h k hih hik hhk, hhzero, hkzero]
  ring

/-- Two different singleton support types cannot coexist at a global maximizer.
No assumptions are imposed on the other physical columns. -/
theorem IsSeparationGlobalMax.threeRow_singleton_rows_eq {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i h : Fin 3) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hb : ThreeRowSingleton P h b) : i = h := by
  by_contra hih
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hki.symm hkh.symm a).mp ha
  have hb' := (threeRowSingleton_iff_other_rows P h i k (Ne.symm hih) hkh.symm hki.symm b).mp hb
  have hda := threeRow_singleton_gradient_difference P i h k hih hki.symm hkh.symm a ha'.2.1 ha'.2.2
  have hdb := threeRow_singleton_gradient_difference P h i k (Ne.symm hih) hkh.symm hki.symm b hb'.2.1 hb'.2.2
  have hga := hmax.threeRow_gradient_le hP (h, a) (i, a) ha'.1
  have hgb := hmax.threeRow_gradient_le hP (i, b) (h, b) hb'.1
  have hr := hmax.row_mass_pos hP (by norm_num : 3 ≤ 3) k
  have hprod := mul_pos hr (add_pos ha'.1 hb'.1)
  dsimp at hga hgb
  nlinarith only [hda, hdb, hga, hgb, hprod]

/-- The exact two-row minor has a strictly negative obstruction from the third row. -/
theorem threeRow_singleton_containing_pair_impossible {a b c x y z : ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z)
    (hcommon : (x + y + z) * (a - b) = (x + y) * c)
    (hmissing : 0 ≤ (x + y) * (a - b) - (x + y + z) * c) : False := by
  have hE : 0 < x + y + z := by linarith
  have heq := congrArg (fun q : ℝ => (x + y) * q) hcommon
  have hineq := mul_nonneg hE.le hmissing
  have hprod := mul_pos (mul_pos hc hz) (by linarith : 0 < 2 * x + 2 * y + z)
  nlinarith only [heq, hineq, hprod]

private theorem sum_fin_three_reindex (f : Fin 3 → ℝ) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) : ∑ l, f l = f i + f h + f k := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> simp_all [Fin.sum_univ_succ] <;> ring

/-- Three-coordinate expansion of the actual column-comparison matrix. -/
theorem threeRowColumnComparison_dot {n : ℕ} (P : Board 3 n) (a b : Fin n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) :
    (∑ l, threeRowColumnComparison P a b i l * (P l a - P l b)) =
      (totalMass P - colSum P a - colSum P b) * (P i a - P i b) +
      (threeRowRemainingRow P a b i + threeRowRemainingRow P a b h) * (P h a - P h b) +
      (threeRowRemainingRow P a b i + threeRowRemainingRow P a b k) * (P k a - P k b) := by
  rw [sum_fin_three_reindex _ i h k hih hik hhk]
  simp only [threeRowColumnComparison, if_true, if_neg hih, if_neg hik]

theorem threeRowRemainingRow_sum_other_rows {n : ℕ} (P : Board 3 n) (a b : Fin n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) :
    threeRowRemainingRow P a b i + threeRowRemainingRow P a b h + threeRowRemainingRow P a b k =
      totalMass P - colSum P a - colSum P b := by
  rw [← sum_fin_three_reindex _ i h k hih hik hhk]
  simp only [threeRowRemainingRow, Finset.sum_sub_distrib]
  rfl

/-- A singleton cannot coexist with a doubleton containing its row.
The excluded row retains positive mass outside the two selected columns. -/
theorem IsSeparationGlobalMax.threeRow_no_singleton_containing_doublet {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i h : Fin 3) (hih : i ≠ h) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hb : ThreeRowDoublet P h b) : False := by
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hki.symm hkh.symm a).mp ha
  have hb' := (threeRowDoublet_iff_other_rows P h i k hih.symm hkh.symm hki.symm b).mp hb
  have hab : a ≠ b := by
    intro heq
    have hz := ha'.2.2
    rw [heq] at hz
    exact (ne_of_gt hb'.2.2) hz
  let x := threeRowRemainingRow P a b i
  let y := threeRowRemainingRow P a b k
  let z := threeRowRemainingRow P a b h
  have hx : 0 ≤ x := threeRowRemainingRow_nonneg hP.1 a b hab i
  have hy : 0 ≤ y := threeRowRemainingRow_nonneg hP.1 a b hab k
  have hz : 0 < z := by
    dsimp [z, threeRowRemainingRow]
    rw [ha'.2.1, hb'.1, sub_zero, sub_zero]
    exact hmax.row_mass_pos hP (by norm_num : 3 ≤ 3) h
  have hs : x + y + z = totalMass P - colSum P a - colSum P b :=
    threeRowRemainingRow_sum_other_rows P a b i k h hki.symm hih hkh
  have hc := hmax.threeRow_comparison_eq_zero hP a b i ha'.1 hb'.2.1
  have hm := hmax.threeRow_comparison_nonneg hP a b k hb'.2.2
  rw [threeRowColumnComparison_dot P a b i k h hki.symm hih hkh,
    ha'.2.1, ha'.2.2, hb'.1, ← hs] at hc
  rw [threeRowColumnComparison_dot P a b k i h hki hkh hih,
    ha'.2.1, ha'.2.2, hb'.1, ← hs] at hm
  apply threeRow_singleton_containing_pair_impossible (a := P i a) (b := P i b) hb'.2.2 hx hy hz
  · change (x + y + z) * (P i a - P i b) + (x + y) * (0 - P k b) +
      (x + z) * (0 - 0) = 0 at hc
    linarith only [hc]
  · change 0 ≤ (x + y + z) * (0 - P k b) + (y + x) * (P i a - P i b) +
      (y + z) * (0 - 0) at hm
    nlinarith only [hm]

/-- All three entries of this physical column are positive. -/
def ThreeRowFullColumn {n : ℕ} (P : Board 3 n) (j : Fin n) : Prop := ∀ i, 0 < P i j

/-- Exhaust the actual support of a nonempty, nonnegative physical column. -/
theorem threeRow_column_support_cases {n : ℕ} {P : Board 3 n} (hP : ∀ i j, 0 ≤ P i j)
    (j : Fin n) (hcol : 0 < colSum P j) : ThreeRowFullColumn P j ∨
      (∃ i, ThreeRowSingleton P i j) ∨ (∃ i, ThreeRowDoublet P i j) := by
  have h0 : P 0 j = 0 ∨ 0 < P 0 j := (eq_or_lt_of_le (hP 0 j)).imp Eq.symm id
  have h1 : P 1 j = 0 ∨ 0 < P 1 j := (eq_or_lt_of_le (hP 1 j)).imp Eq.symm id
  have h2 : P 2 j = 0 ∨ 0 < P 2 j := (eq_or_lt_of_le (hP 2 j)).imp Eq.symm id
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hz : colSum P j = 0 := by simp [colSum, Fin.sum_univ_succ, h0, h1, h2]
    exact False.elim ((ne_of_gt hcol) hz)
  · right; left; refine ⟨2, ?_⟩
    simpa [ThreeRowSingleton] using And.intro h2 (And.intro h0 h1)
  · right; left; refine ⟨1, ?_⟩
    simpa [ThreeRowSingleton] using And.intro h1 (And.intro h2 h0)
  · right; right; exact ⟨0, h0, h1, h2⟩
  · right; left; exact ⟨0, h0, h1, h2⟩
  · right; right; refine ⟨1, ?_⟩
    simpa [ThreeRowDoublet] using And.intro h1 (And.intro h2 h0)
  · right; right; refine ⟨2, ?_⟩
    simpa [ThreeRowDoublet] using And.intro h2 (And.intro h0 h1)
  · left
    intro i
    fin_cases i <;> assumption

/-- If a singleton occurs, every remaining column is its own singleton type,
the opposite doubleton, or full. No multiplicity bound is introduced. -/
theorem IsSeparationGlobalMax.threeRow_supports_of_singleton {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a : Fin n) (ha : ThreeRowSingleton P i a) (b : Fin n) :
    ThreeRowSingleton P i b ∨ ThreeRowDoublet P i b ∨ ThreeRowFullColumn P b := by
  rcases threeRow_column_support_cases hP.1 b (hmax.column_mass_pos hP hn b) with hf | ⟨h, hs⟩ | ⟨h, hd⟩
  · exact Or.inr (Or.inr hf)
  · have heq := hmax.threeRow_singleton_rows_eq hP i h a b ha hs
    exact Or.inl (heq.symm ▸ hs)
  · by_cases heq : i = h
    · exact Or.inr (Or.inl (heq.symm ▸ hd))
    · exact False.elim (hmax.threeRow_no_singleton_containing_doublet hP i h heq a b ha hd)

end DittertRybin
