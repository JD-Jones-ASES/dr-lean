import DR.Endpoint.PermanentFaceDirections
import Mathlib.Combinatorics.Hall.Basic

/-! Strict Hall support implies positivity of every actual permanental cofactor.
The matching is constructed after forcing its selected row-column pair. -/

namespace DittertRybin
open scoped BigOperators

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def permanentSupportNeighbors (A : Matrix ι ι ℝ) (S : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∃ j ∈ S, 0 < A i j

omit [DecidableEq ι] in
@[simp] theorem mem_permanentSupportNeighbors (A : Matrix ι ι ℝ) (S : Finset ι) (i : ι) :
    i ∈ permanentSupportNeighbors A S ↔ ∃ j ∈ S, 0 < A i j := by
  classical
  simp [permanentSupportNeighbors]

/-- Every nonempty proper set of columns has strictly more neighboring rows. -/
def StrictPermanentHall (A : Matrix ι ι ℝ) : Prop :=
  ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
    S.card < (permanentSupportNeighbors A S).card

theorem StrictPermanentHall.forced_matching {A : Matrix ι ι ℝ}
    (hA : StrictPermanentHall A) (i j : ι) :
    ∃ σ : Equiv.Perm ι, σ j = i ∧ ∀ k, k ≠ j → 0 < A (σ k) k := by
  classical
  let R : ι → ι → Prop := fun k r => if k = j then r = i else r ≠ i ∧ 0 < A r k
  have hall : ∀ S : Finset ι,
      S.card ≤ (Finset.univ.filter fun r => ∃ k ∈ S, R k r).card := by
    intro S
    by_cases hj : j ∈ S
    · by_cases he : (S.erase j).Nonempty
      · have hp : S.erase j ≠ Finset.univ := by
          intro h
          have := congrArg (fun T : Finset ι => j ∈ T) h
          simp at this
        have hs := hA (S.erase j) he hp
        have hsub : permanentSupportNeighbors A (S.erase j) ⊆
            Finset.univ.filter fun r => ∃ k ∈ S, R k r := by
          intro r hr
          obtain ⟨k, hk, hpos⟩ := (mem_permanentSupportNeighbors _ _ _).mp hr
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          by_cases hri : r = i
          · exact ⟨j, hj, by simp [R, hri]⟩
          · exact ⟨k, (Finset.mem_erase.mp hk).2,
              by simp [R, (Finset.mem_erase.mp hk).1, hri, hpos]⟩
        have hc := Finset.card_le_card hsub
        have her := Finset.card_erase_add_one hj
        omega
      · have hempty : S.erase j = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        have hs : S.card = 1 := by
          have := Finset.card_erase_add_one hj
          simp [hempty] at this
          omega
        rw [hs]
        apply Finset.one_le_card.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩⟩
        simp [R]
    · by_cases he : S.Nonempty
      · have hp : S ≠ Finset.univ := by intro h; exact hj (h ▸ Finset.mem_univ j)
        have hs := hA S he hp
        have hsub : (permanentSupportNeighbors A S).erase i ⊆
            Finset.univ.filter fun r => ∃ k ∈ S, R k r := by
          intro r hr
          obtain ⟨hri, hr⟩ := Finset.mem_erase.mp hr
          obtain ⟨k, hk, hpos⟩ := (mem_permanentSupportNeighbors _ _ _).mp hr
          have hkj : k ≠ j := by intro h; exact hj (h ▸ hk)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk,
            by simp [R, hkj, hri, hpos]⟩
        have hc := Finset.card_le_card hsub
        have hin : (permanentSupportNeighbors A S).card ≤
            ((permanentSupportNeighbors A S).erase i).card+1 := by
          by_cases hi : i ∈ permanentSupportNeighbors A S
          · exact (Finset.card_erase_add_one hi).ge
          · simp [Finset.erase_eq_of_notMem hi]
        omega
      · simp [Finset.not_nonempty_iff_eq_empty.mp he]
  obtain ⟨f, hf, hR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hall
  let σ : Equiv.Perm ι := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  refine ⟨σ, ?_, ?_⟩
  · simpa [R, σ] using hR j
  · intro k hkj
    exact (by simpa [R, hkj, σ] using hR k : σ k ≠ i ∧ 0 < A (σ k) k).2

theorem StrictPermanentHall.cofactor_pos {A : Matrix ι ι ℝ}
    (hA : StrictPermanentHall A) (hnonneg : ∀ i j, 0 ≤ A i j) (i j : ι) :
    0 < permanentalCofactor A i j :=
  (permanentalCofactor_pos_iff hnonneg i j).mpr (hA.forced_matching i j)

end
end DittertRybin
