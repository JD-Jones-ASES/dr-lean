import DR.Rectangular.ThreeRowFullOffsets

/-! Three doubleton types are incompatible with full columns at a global maximum. -/

namespace DittertRybin
open scoped BigOperators

/-- Two strict residual majorities contradict the reversed full-column offsets. -/
theorem IsSeparationGlobalMax.threeRow_ordered_three_doublets_impossible {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hsame : ThreeRowFullColumnsEqual P) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hrih : rowSum P h < rowSum P i) (hrhk : rowSum P k < rowSum P h)
    (a b c : Fin n) (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (hc : ThreeRowDoublet P k c) (q : Fin n) (hq : ThreeRowFullColumn P q) : False := by
  have hoih := hmax.threeRow_full_column_offset hP hn hsame i h k hih hik hhk b hb q hq hrih
  have hoik := hmax.threeRow_full_column_offset hP hn hsame i k h hik hih hhk.symm c hc q hq (hrhk.trans hrih)
  have hohk := hmax.threeRow_full_column_offset hP hn hsame h k i hhk hih.symm hik.symm c hc q hq hrhk
  have hentry := hmax.threeRow_doublet_exclusive_order hP hn i h hih a b ha hb hrih
  have hoffset : P h a + P i c < 2 * P k q := by
    linarith only [hoih, hoik, hohk, hentry, hq i, hP.1 h c]
  have hm1 := hmax.threeRow_full_pair_majority hP i h k hih hik hhk a b ha hb q hq hrih
  have hm2 := hmax.threeRow_full_pair_majority hP h k i hhk hih.symm hik.symm b c hb hc q hq hrhk
  unfold threeRowRemainingRow at hm1 hm2
  rw [ha.1, hb.1] at hm1
  rw [hb.1, hc.1] at hm2
  have hab : a ≠ b := by
    intro hab
    exact hih (hb.missing_unique i (hab ▸ ha.1))
  have hqa : q ≠ a := by
    intro hqa
    exact (ne_of_gt (hq i)) (hqa.symm ▸ ha.1)
  have hqb : q ≠ b := by
    intro hqb
    exact (ne_of_gt (hq h)) (hqb.symm ▸ hb.1)
  have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    eraseColumns_nonneg hP.1 {a, b} k j) (Finset.mem_univ q)
  change eraseColumns P {a, b} k q ≤ rowSum (eraseColumns P {a, b}) k at he
  rw [rowSum_eraseColumns_pair P a b hab k] at he
  simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hqa, hqb, or_self, if_false] at he
  linarith only [hm1, hm2, he, hoffset, hP.1 k a, hP.1 h c]

private theorem three_row_strict_order (r : Fin 3 → ℝ)
    (h01 : r 0 ≠ r 1) (h02 : r 0 ≠ r 2) (h12 : r 1 ≠ r 2) :
    ∃ i h k : Fin 3, i ≠ h ∧ i ≠ k ∧ h ≠ k ∧ r h < r i ∧ r k < r h := by
  rcases lt_or_gt_of_ne h01 with h01 | h10
  · rcases lt_or_gt_of_ne h12 with h12 | h21
    · exact ⟨2, 1, 0, by decide, by decide, by decide, h12, h01⟩
    · rcases lt_or_gt_of_ne h02 with h02 | h20
      · exact ⟨1, 2, 0, by decide, by decide, by decide, h21, h02⟩
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h01, h20⟩
  · rcases lt_or_gt_of_ne h02 with h02 | h20
    · exact ⟨2, 0, 1, by decide, by decide, by decide, h02, h10⟩
    · rcases lt_or_gt_of_ne h12 with h12 | h21
      · exact ⟨0, 2, 1, by decide, by decide, by decide, h20, h12⟩
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h10, h21⟩

/-- Every three-row global maximum omits at least one doubleton support type. -/
theorem IsSeparationGlobalMax.threeRow_not_all_doublet_types {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (htypes : ∀ i, ∃ a, ThreeRowDoublet P i a) : False := by
  obtain ⟨q, hq⟩ := hmax.threeRow_exists_full_column hP hn
  obtain ⟨ε, Q, hε, hQ, hQmax, hfloor, hsame⟩ := exists_threeRow_full_equal_normal_form hP hmax
  have hqQ := hfloor.threeRowFullColumn hε hq
  have htypesQ (i : Fin 3) : ∃ a, ThreeRowDoublet Q i a := by
    obtain ⟨a, ha⟩ := htypes i
    exact ⟨a, hfloor.threeRowDoublet hε ha⟩
  have hne (i h : Fin 3) (hih : i ≠ h) : rowSum Q i ≠ rowSum Q h := by
    obtain ⟨a, ha⟩ := htypesQ i
    obtain ⟨b, hb⟩ := htypesQ h
    exact hQmax.threeRow_full_pair_row_masses_ne hQ hn i h hih a b ha hb q hqQ
  obtain ⟨i, h, k, hih, hik, hhk, hrih, hrhk⟩ := three_row_strict_order (rowSum Q)
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
  obtain ⟨a, ha⟩ := htypesQ i
  obtain ⟨b, hb⟩ := htypesQ h
  obtain ⟨c, hc⟩ := htypesQ k
  exact hQmax.threeRow_ordered_three_doublets_impossible hQ hn hsame i h k hih hik hhk hrih hrhk a b c ha hb hc q hqQ

end DittertRybin
