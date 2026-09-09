import DR.Rectangular.FourRowMinorantThreeVariation

/-! The actual corrected minorant on every proper column-distribution face.
Compact minimization, the singular discriminant, stationary feasibility,
and all row/column boundary cases are proved inputs of this theorem. -/

namespace DittertRybin
open scoped BigOperators

theorem fourRowMinorantHomogeneous_three_face_positive_rows (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous ![a,b,c,d] v := by
  let r : Fin 4 → ℝ := ![a,b,c,d]
  obtain ⟨u,hu,hus,hu3,hmin,htie⟩ := exists_threeFace_minorant_minimum_max_norm r
  have hr : ∀ i, 0 < r i := by
    intro i; fin_cases i <;> assumption
  have hm : 0 < ∑ i,r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hnon : 0 ≤ fourRowMinorantHomogeneous r u := by
    by_cases hpos : ∀ i, i ≠ 3 → 0 < u i
    · have hD := hmin.discriminant_pos htie ha hb hc hd hpos hus hu3
      have heq := hmin.eq_stationary htie ha hb hc hd hpos hus hu3
      rw [heq]
      exact fourRowThreeStationary_feasible_nonneg a b c d ha.le hb.le hc.le hd hD
        (by intro i; rw [←heq]; exact hu i)
    · push Not at hpos
      obtain ⟨i,hi,hi0⟩ := hpos
      have hz : u i=0 := le_antisymm hi0 (hu i)
      fin_cases i
      · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r u (fun j => (hr j).le)
          hm hu hus 1 2 (by decide)
        intro k hk1 hk2
        fin_cases k <;> first | contradiction | exact hz | exact hu3
      · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r u (fun j => (hr j).le)
          hm hu hus 0 2 (by decide)
        intro k hk0 hk2
        fin_cases k <;> first | contradiction | exact hz | exact hu3
      · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r u (fun j => (hr j).le)
          hm hu hus 0 1 (by decide)
        intro k hk0 hk1
        fin_cases k <;> first | contradiction | exact hz | exact hu3
      · exact False.elim (hi rfl)
  exact hnon.trans (hmin v hv hvs hv3)

theorem fourRowMinorantHomogeneous_zero_last_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∑ i,r i=1)
    (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  by_cases hpos : ∀ i, 0 < r i
  · have heq : r=![r 0,r 1,r 2,r 3] := by
      funext i; fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three]
    have h := fourRowMinorantHomogeneous_three_face_positive_rows (r 0) (r 1) (r 2) (r 3)
      (hpos 0) (hpos 1) (hpos 2) (hpos 3) v hv hvs hv3
    rwa [←heq] at h
  · push Not at hpos
    obtain ⟨i,hi⟩ := hpos
    exact fourRowMinorantHomogeneous_boundary_nonneg r v hr hs hv hvs
      ⟨i,le_antisymm hi (hr i)⟩

/-- Every proper face of v on both full closed probability simplices. -/
theorem fourRowMinorantHomogeneous_proper_face_nonneg (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∑ i,r i=1)
    (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i,v i=1) (hz : ∃ i,v i=0) :
    0 ≤ fourRowMinorantHomogeneous r v := by
  classical
  obtain ⟨i,hi⟩ := hz
  let e := Equiv.swap (3 : Fin 4) i
  have h := fourRowMinorantHomogeneous_zero_last_nonneg (r ∘ e) (v ∘ e)
    (fun j => hr (e j)) ((Equiv.sum_comp e r).trans hs)
    (fun j => hv (e j)) ((Equiv.sum_comp e v).trans hvs)
    (by simp [e,Function.comp_apply,hi])
  rwa [fourRowMinorantHomogeneous_permute] at h

end DittertRybin
