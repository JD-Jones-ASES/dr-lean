import DR.Rectangular.ThreeRowSingleDoubletBoard
import DR.Rectangular.ThreeRowSingleDoubletScalar

/-! Actual support reduction and exclusion of the one-doubleton boundary family. -/
namespace DittertRybin
open scoped BigOperators

/-- Every row other than the unique missing row of a doubleton is strictly positive. -/
theorem ThreeRowDoublet.pos_of_ne {n : ℕ} {P : Board 3 n} {i : Fin 3} {j : Fin n}
    (hj : ThreeRowDoublet P i j) (r : Fin 3) (hri : r ≠ i) : 0 < P r j := by
  rcases (by decide : ∀ i r : Fin 3, r ≠ i → r = i+1 ∨ r = i+2) i r hri with hr | hr
  · simpa only [hr] using hj.2.1
  · simpa only [hr] using hj.2.2

/-- A single occurring doubleton type yields a genuine two-class global representative.
Both classes are nonempty and every originally positive entry stays positive. -/
theorem IsSeparationGlobalMax.threeRow_single_doublet_representative {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a : Fin n) (ha : ThreeRowDoublet P i a)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i) :
    ∃ (s : Finset (Fin n)) (b c d : ℝ), s.Nonempty ∧ sᶜ.Nonempty ∧
      0 < b ∧ 0 < c ∧ 0 < d ∧ IsProbability (threeRowSingleDoubletBoard i s b c d) ∧
      IsSeparationGlobalMax (threeRowSingleDoubletBoard i s b c d) 3 := by
  classical
  obtain ⟨q, hq⟩ := hmax.threeRow_exists_full_column hP hn
  obtain ⟨ε, Q, hε, hQ, hQmax, hfloor, hcols, hrows⟩ :=
    exists_same_support_normal_form hP hmax (by norm_num : 2 ≤ 3)
  have hcases (j : Fin n) : ThreeRowFullColumn P j ∨ ThreeRowDoublet P i j := by
    rcases hmax.threeRow_columns_full_or_doublet hP hn j with hf | ⟨r, hr⟩
    · exact Or.inl hf
    · exact Or.inr (htypes r j hr ▸ hr)
  have hpos (r : Fin 3) (hri : r ≠ i) (j : Fin n) : 0 < P r j := by
    rcases hcases j with hf | hd
    · exact hf r
    · exact hd.pos_of_ne r hri
  let h : Fin 3 := i+1
  have hhi : h ≠ i := (by decide : ∀ i : Fin 3, i+1 ≠ i) i
  let s := Finset.univ.filter (fun j => P i j = 0)
  have hmem (j : Fin n) : j ∈ s ↔ P i j = 0 := by simp [s]
  have haS : a ∈ s := (hmem a).mpr ha.1
  have hqS : q ∉ s := fun hh => (ne_of_gt (hq i)) ((hmem q).mp hh)
  have hrowsQ (r : Fin 3) (hri : r ≠ i) (j : Fin n) : Q r j = Q h j :=
    hrows r h (fun c => iff_of_true (hpos r hri c) (hpos h hhi c)) j
  have hcolsA (j : Fin n) (hj : j ∈ s) (r : Fin 3) : Q r j = Q r a := by
    apply hcols j a
    intro t
    by_cases hti : t = i
    · subst t
      rw [(hmem j).mp hj, ha.1]
    · exact iff_of_true (hpos t hti j) (hpos t hti a)
  have hcolsQ (j : Fin n) (hj : j ∉ s) (r : Fin 3) : Q r j = Q r q := by
    apply hcols j q
    intro t
    rcases hcases j with hf | hd
    · exact iff_of_true (hf t) (hq t)
    · exact False.elim (hj ((hmem j).mpr hd.1))
  have hshape : Q = threeRowSingleDoubletBoard i s (Q h a) (Q i q) (Q h q) := by
    funext r j
    unfold threeRowSingleDoubletBoard
    by_cases hri : r = i
    · subst r
      simp only [if_true]
      by_cases hj : j ∈ s
      · rw [if_pos hj]
        exact (hfloor i j).1 ((hmem j).mp hj)
      · rw [if_neg hj]
        exact hcolsQ j hj i
    · rw [if_neg hri, hrowsQ r hri j]
      by_cases hj : j ∈ s
      · rw [if_pos hj]
        exact hcolsA j hj h
      · rw [if_neg hj]
        exact hcolsQ j hj h
  refine ⟨s, Q h a, Q i q, Q h q, ⟨a, haS⟩, ⟨q, by simpa using hqS⟩,
    hε.trans_le ((hfloor h a).2 (hpos h hhi a)),
    hε.trans_le ((hfloor i q).2 (hq i)),
    hε.trans_le ((hfloor h q).2 (hq h)), ?_, ?_⟩
  · rwa [← hshape]
  · rwa [← hshape]

/-- The full-simplex zero inequalities exclude every matrix with exactly one
occurring doubleton type, for arbitrary physical column counts at least three. -/
theorem IsSeparationGlobalMax.threeRow_not_single_doublet_type {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a : Fin n) (ha : ThreeRowDoublet P i a)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i) : False := by
  classical
  obtain ⟨s,b,c,d,hS,hT,hb,hc,hd,hQ,hQmax⟩ :=
    hmax.threeRow_single_doublet_representative hP hn i a ha htypes
  obtain ⟨a, ha⟩ := hS
  obtain ⟨q, hq⟩ := hT
  have hq' : q ∉ s := Finset.mem_compl.mp hq
  have hih : i ≠ i+1 := (by decide : ∀ i : Fin 3, i ≠ i+1) i
  have hik : i ≠ i+2 := (by decide : ∀ i : Fin 3, i ≠ i+2) i
  have hhk : i+1 ≠ i+2 := (by decide : ∀ i : Fin 3, i+1 ≠ i+2) i
  obtain ⟨hcol,hcolzero,hrow,hrowzero⟩ := hQmax.threeRow_single_doublet_board_kkt
    i (i+1) (i+2) hih hik hhk s b c d hb hc hd a q ha hq' hQ
  have hcount : s.card + sᶜ.card = n := by simp
  apply threeRow_single_doublet_full_kkt_impossible
    (show 1 ≤ s.card from Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨a,ha⟩))
    (show 1 ≤ sᶜ.card from Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨q,hq⟩))
    (by omega) hb hc hd
  · nlinarith only [hcol]
  · nlinarith only [hcolzero]
  · exact hrow
  · linarith only [hrowzero]

end DittertRybin
