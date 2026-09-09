import DR.Rectangular.ThreeRowSingletons
import DR.Square.OrderThreeFinal

/-! An actual global maximizer cannot consist entirely of doubleton columns. -/

namespace DittertRybin
open scoped BigOperators

/-- A doubleton has exactly one missing row. -/
theorem ThreeRowDoublet.missing_unique {n : ℕ} {P : Board 3 n} {i : Fin 3} {a : Fin n}
    (ha : ThreeRowDoublet P i a) (h : Fin 3) (hh : P h a = 0) : h = i := by
  by_contra hhi
  have hih : i ≠ h := Ne.symm hhi
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have hp := (threeRowDoublet_iff_other_rows P i h k hih hki.symm hkh.symm a).mp ha
  exact (ne_of_gt hp.2.1) hh

/-- Equal omitted-row masses force zero residual mass in their common occupied row. -/
theorem IsSeparationGlobalMax.threeRow_doublet_common_remaining_zero {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (a b : Fin n) (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (hrow : rowSum P i = rowSum P h) : threeRowRemainingRow P a b k = 0 := by
  by_cases hh : h = i + 2
  · have hk : k = i + 1 :=
      (by decide : ∀ i h k : Fin 3, i ≠ h → i ≠ k → h ≠ k → h = i + 2 → k = i + 1) i h k hih hik hhk hh
    subst h
    have hz := (hmax.threeRow_doublet_equal_rows hP hn i a b ha hb hrow).2.2.1
    simpa only [hk] using hz
  · have hi : i = h + 2 :=
      (by decide : ∀ i h : Fin 3, i ≠ h → h ≠ i + 2 → i = h + 2) i h hih hh
    have hk : k = h + 1 :=
      (by decide : ∀ h i k : Fin 3, h ≠ i → h ≠ k → i ≠ k → i = h + 2 → k = h + 1) h i k hih.symm hhk hik hi
    subst i
    have hz := (hmax.threeRow_doublet_equal_rows hP hn h b a hb ha hrow.symm).2.2.1
    unfold threeRowRemainingRow at hz ⊢
    rw [hk]
    linarith only [hz]

/-- A zero residual row sum means every actual entry outside the two columns is zero. -/
theorem threeRow_entry_zero_of_remaining_zero {n : ℕ} {P : Board 3 n}
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n) (hab : a ≠ b) (i : Fin 3)
    (hzero : threeRowRemainingRow P a b i = 0) (c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) :
    P i c = 0 := by
  have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    eraseColumns_nonneg hP {a, b} i j) (Finset.mem_univ c)
  change eraseColumns P {a, b} i c ≤ rowSum (eraseColumns P {a, b}) i at he
  rw [rowSum_eraseColumns_pair P a b hab i] at he
  change eraseColumns P {a, b} i c ≤ threeRowRemainingRow P a b i at he
  rw [hzero] at he
  simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hca, hcb, or_self, if_false] at he
  exact le_antisymm he (hP i c)

/-- Doubleton-only global supports have at most three physical columns, not merely three types. -/
theorem IsSeparationGlobalMax.threeRow_doublet_only_dimension {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hcols : ∀ c, ∃ i, ThreeRowDoublet P i c) : n ≤ 3 := by
  have hproper : ThreeRowProperSupport P := fun c => by
    obtain ⟨i, hi⟩ := hcols c
    exact ⟨i, hi.1⟩
  let a : Fin n := ⟨0, by omega⟩
  obtain ⟨i, ha⟩ := hcols a
  have hr := hmax.row_mass_pos hP (by norm_num : 3 ≤ 3) i
  obtain ⟨b, _hb, hbi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hP.1 i j)).mp hr
  obtain ⟨h, hb⟩ := hcols b
  have hih : i ≠ h := by
    intro heq
    exact (ne_of_gt hbi) (heq ▸ hb.1)
  have hab : a ≠ b := by
    intro heq
    exact (ne_of_gt hbi) (heq ▸ ha.1)
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have hrow := hmax.threeRow_proper_doublet_row_masses_eq hP hn hproper i h a b ha hb
  have hkab := hmax.threeRow_doublet_common_remaining_zero hP hn i h k hih hki.symm hkh.symm a b ha hb hrow
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hkc := threeRow_entry_zero_of_remaining_zero hP.1 a b hab k hkab c hca hcb
  obtain ⟨l, hc'⟩ := hcols c
  have hl : k = l := hc'.missing_unique k hkc
  have hc : ThreeRowDoublet P k c := hl.symm ▸ hc'
  have hrow' := hmax.threeRow_proper_doublet_row_masses_eq hP hn hproper i k a c ha hc
  have hhac := hmax.threeRow_doublet_common_remaining_zero hP hn i k h hki.symm hih hkh a c ha hc hrow'
  have hcover (d : Fin n) : d = a ∨ d = b ∨ d = c := by
    by_cases hda : d = a
    · exact Or.inl hda
    by_cases hdb : d = b
    · exact Or.inr (Or.inl hdb)
    by_cases hdc : d = c
    · exact Or.inr (Or.inr hdc)
    have hkd := threeRow_entry_zero_of_remaining_zero hP.1 a b hab k hkab d hda hdb
    have hhd := threeRow_entry_zero_of_remaining_zero hP.1 a c hca.symm h hhac d hda hdc
    obtain ⟨q, hq⟩ := hcols d
    exact False.elim (hkh ((hq.missing_unique k hkd).trans (hq.missing_unique h hhd).symm))
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcover d
  have hcard : ({a, b, c} : Finset (Fin n)).card = 3 := by simp [hab, hca.symm, hcb.symm]
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_univ, Fintype.card_fin, hcard] using hh

/-- The three-column endpoint is discharged by the independently established square theorem. -/
theorem IsSeparationGlobalMax.threeRow_not_doublet_only {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hcols : ∀ c, ∃ i, ThreeRowDoublet P i c) : False := by
  have hn3 : n = 3 := by
    have hh := hmax.threeRow_doublet_only_dimension hP hn hcols
    omega
  subst n
  have hu := uniformMaximizer_three_three_three P hP
  have hl := hmax _ (uniformBoard_isProbability (by norm_num : 0 < 3) (by norm_num : 0 < 3))
  rw [separationProbability_uniform (by norm_num : 0 < 3) (by norm_num : 0 < 3)] at hl
  have heq := hu.2.mp (le_antisymm hu.1 hl)
  obtain ⟨i, hi⟩ := hcols 0
  have hz := hi.1
  rw [heq] at hz
  norm_num [uniformBoard] at hz

end DittertRybin
