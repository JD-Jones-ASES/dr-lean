import DR.Rectangular.ThreeRowTwoDoublets

/-! Support-preserving normalization closes the arbitrary two-doubleton family. -/
namespace DittertRybin

/-- A support floor preserves doubleton types in both directions on the closed simplex. -/
theorem SameSupportFloor.threeRowDoublet_iff {n : ℕ} {P Q : Board 3 n} {ε : ℝ}
    (hfloor : SameSupportFloor P ε Q) (hP : ∀ i j, 0 ≤ P i j) (hε : 0 < ε)
    (i : Fin 3) (a : Fin n) : ThreeRowDoublet Q i a ↔ ThreeRowDoublet P i a := by
  constructor
  · intro ha
    refine ⟨?_, (hfloor.support_iff hP hε (i+1) a).mp ha.2.1,
      (hfloor.support_iff hP hε (i+2) a).mp ha.2.2⟩
    by_contra hne
    have hp : 0 < P i a := lt_of_le_of_ne (hP i a) (Ne.symm hne)
    exact (ne_of_gt ((hfloor.support_iff hP hε i a).mpr hp)) ha.1
  · exact hfloor.threeRowDoublet hε

/-- One actual maximizer has identical full columns and identical doubletons of each type. -/
theorem exists_threeRow_equal_columns_normal_form {n : ℕ} {P : Board 3 n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3) :
    ∃ (ε : ℝ) (Q : Board 3 n), 0 < ε ∧ IsProbability Q ∧ IsSeparationGlobalMax Q 3 ∧
      SameSupportFloor P ε Q ∧ ThreeRowFullColumnsEqual Q ∧ ThreeRowDoubletColumnsEqual Q := by
  obtain ⟨ε,Q,hε,hQ,hQmax,hfloor,hcols,_hrows⟩ :=
    exists_same_support_normal_form hP hmax (by norm_num : 2 ≤ 3)
  refine ⟨ε,Q,hε,hQ,hQmax,hfloor,?_,?_⟩
  · intro a b ha hb
    apply hcols a b
    intro i
    exact iff_of_true ((hfloor.support_iff hP.1 hε i a).mp (ha i))
      ((hfloor.support_iff hP.1 hε i b).mp (hb i))
  · intro i a b ha hb
    have haP := (hfloor.threeRowDoublet_iff hP.1 hε i a).mp ha
    have hbP := (hfloor.threeRowDoublet_iff hP.1 hε i b).mp hb
    apply hcols a b
    intro r
    by_cases hri : r = i
    · subst r
      rw [haP.1,hbP.1]
    · exact iff_of_true (haP.pos_of_ne r hri) (hbP.pos_of_ne r hri)

/-- Two occurring doubleton types, with all remaining columns full or of those types,
are impossible at an actual global maximum. -/
theorem IsSeparationGlobalMax.threeRow_not_two_doublet_types {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h : Fin 3) (hih : i ≠ h) (a b : Fin n)
    (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i ∨ r = h) : False := by
  obtain ⟨q,hq⟩ := hmax.threeRow_exists_full_column hP hn
  obtain ⟨ε,Q,hε,hQ,hQmax,hfloor,hsame,hdouble⟩ := exists_threeRow_equal_columns_normal_form hP hmax
  have haQ := hfloor.threeRowDoublet hε ha
  have hbQ := hfloor.threeRowDoublet hε hb
  have hqQ := hfloor.threeRowFullColumn hε hq
  have htypesQ (r : Fin 3) (j : Fin n) (hj : ThreeRowDoublet Q r j) : r = i ∨ r = h :=
    htypes r j ((hfloor.threeRowDoublet_iff hP.1 hε r j).mp hj)
  have hne := hQmax.threeRow_full_pair_row_masses_ne hQ hn i h hih a b haQ hbQ q hqQ
  obtain ⟨k,hki,hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hQmax.threeRow_ordered_two_doublets_impossible hQ hn hsame hdouble h i k hih.symm hkh.symm hki.symm
      b a hbQ haQ q hqQ hlt (fun r j hj => (htypesQ r j hj).symm)
  · exact hQmax.threeRow_ordered_two_doublets_impossible hQ hn hsame hdouble i h k hih hki.symm hkh.symm
      a b haQ hbQ q hqQ hgt htypesQ

end DittertRybin
