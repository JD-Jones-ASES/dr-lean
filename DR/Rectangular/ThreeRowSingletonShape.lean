import DR.Rectangular.ThreeRowSingletonSymmetry
import DR.Rectangular.ThreeRowSupportNormal

/-! Actual support-preserving reduction of a singleton global maximizer to a two-star board. -/

namespace DittertRybin
open scoped BigOperators

private theorem three_row_exhaust (i h k r : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) :
    r = i ∨ r = h ∨ r = k := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> fin_cases r <;> simp_all

private theorem three_row_colsum (P : Board 3 n) (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (c : Fin n) :
    colSum P c = P i c + P h c + P k c := by
  fin_cases i <;> fin_cases h <;> fin_cases k <;> simp_all [colSum, Fin.sum_univ_succ] <;> ring

/-- Every entry in the singleton row away from the opposite column has the same value. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_own_entries {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) (c : Fin n) (hcb : c ≠ b) : P i c = P i a := by
  have hhc := hmax.threeRow_symmetric_singleton_other_zero hP hn i h k hih hik hhk hsym a ha b hb c hcb
  have hkc : P k c = 0 := (hsym c).symm.trans hhc
  have hcol := hmax.column_mass_pos hP hn c
  rw [three_row_colsum P i h k hih hik hhk c, hhc, hkc, add_zero, add_zero] at hcol
  have hc : ThreeRowSingleton P i c :=
    (threeRowSingleton_iff_other_rows P i h k hih hik hhk c).mpr ⟨hcol, hhc, hkc⟩
  have hec := hmax.threeRow_symmetric_singleton_opposite_entries hP hn i h k hih hik hhk hsym c hc b hb
  have hea := hmax.threeRow_symmetric_singleton_opposite_entries hP hn i h k hih hik hhk hsym a ha b hb
  exact hec.2.symm.trans hea.2

/-- A row-symmetric singleton global maximizer has exactly the two-star physical entries. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_shape {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a) :
    ∃ b : Fin n, ∀ r c, P r c =
      if r = i then (if c = b then 0 else P i a) else (if c = b then P i a else 0) := by
  have hr := hmax.row_mass_pos hP (by norm_num : 3 ≤ 3) h
  obtain ⟨b, _hb, hb⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hP.1 h j)).mp hr
  have he := hmax.threeRow_symmetric_singleton_opposite_entries hP hn i h k hih hik hhk hsym a ha b hb
  have hh (c : Fin n) : P h c = if c = b then P i a else 0 := by
    by_cases hcb : c = b
    · simpa only [hcb, if_true] using he.2
    · simpa only [if_neg hcb] using
        hmax.threeRow_symmetric_singleton_other_zero hP hn i h k hih hik hhk hsym a ha b hb c hcb
  refine ⟨b, ?_⟩
  intro r c
  by_cases hri : r = i
  · subst r
    simp only [if_true]
    by_cases hcb : c = b
    · simpa only [hcb, if_true] using he.1
    · simpa only [if_neg hcb] using
        hmax.threeRow_symmetric_singleton_own_entries hP hn i h k hih hik hhk hsym a ha b hb c hcb
  · simp only [if_neg hri]
    rcases three_row_exhaust i h k r hih hik hhk with hr | hr | hr
    · exact False.elim (hri hr)
    · simpa only [hr] using hh c
    · simpa only [hr, ← hsym c] using hh c

/-- With a singleton present, the other two rows have the same actual positive support. -/
theorem IsSeparationGlobalMax.threeRow_singleton_other_supports {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (a : Fin n) (ha : ThreeRowSingleton P i a) : ∀ j, 0 < P h j ↔ 0 < P k j := by
  intro j
  rcases hmax.threeRow_supports_of_singleton hP hn i a ha j with hs | hd | hf
  · have hs' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk j).mp hs
    rw [hs'.2.1, hs'.2.2]
  · have hd' := (threeRowDoublet_iff_other_rows P i h k hih hik hhk j).mp hd
    exact iff_of_true hd'.2.1 hd'.2.2
  · exact iff_of_true (hf h) (hf k)

/-- Every singleton global maximizer would have a genuine two-star global representative.
Its specified zeros and the positive entries used in the reduction are retained. -/
theorem IsSeparationGlobalMax.threeRow_singleton_global_representative {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a : Fin n) (ha : ThreeRowSingleton P i a) :
    ∃ (Q : Board 3 n) (b : Fin n) (u : ℝ), IsProbability Q ∧ IsSeparationGlobalMax Q 3 ∧
      0 < u ∧ ∀ r c, Q r c = if r = i then (if c = b then 0 else u) else (if c = b then u else 0) := by
  let h := i + 1
  let k := i + 2
  have hih : i ≠ h := by dsimp [h]; fin_cases i <;> decide
  have hik : i ≠ k := by dsimp [k]; fin_cases i <;> decide
  have hhk : h ≠ k := by dsimp [h, k]; fin_cases i <;> decide
  have hs := hmax.threeRow_singleton_other_supports hP hn i h k hih hik hhk a ha
  obtain ⟨ε, Q, hε, hQ, hQmax, hfloor, _hcols, hrows⟩ :=
    exists_same_support_normal_form hP hmax (by norm_num : 2 ≤ 3)
  have hsym : ∀ j, Q h j = Q k j := hrows h k hs
  have haQ : ThreeRowSingleton Q i a := by
    refine ⟨hε.trans_le ((hfloor i a).2 ha.1), ?_, ?_⟩
    · exact (hfloor (i + 1) a).1 ha.2.1
    · exact (hfloor (i + 2) a).1 ha.2.2
  obtain ⟨b, hb⟩ := hQmax.threeRow_symmetric_singleton_shape hQ hn i h k hih hik hhk hsym a haQ
  exact ⟨Q, b, Q i a, hQ, hQmax, haQ.1, hb⟩

end DittertRybin
