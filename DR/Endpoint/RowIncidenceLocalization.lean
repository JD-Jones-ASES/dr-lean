import DR.Endpoint.RowDeletionExpectation
import DR.Endpoint.RowCollisionLocalized

/-! Connecting actual participation indicators to the increasing-pair
indices of the localized collision estimates. -/

namespace DittertRybin
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

theorem samplePair_rows_injective {m : ℕ} :
    Function.Injective (fun e : SampleIndexPair m => ({e.val.1,e.val.2} : Finset (Fin m))) := by
  intro e f he
  dsimp only at he
  have h1 : e.val.1=f.val.1 ∨ e.val.1=f.val.2 := by
    have hmem : e.val.1∈({f.val.1,f.val.2} : Finset (Fin m)) := by rw [← he]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem
  have h2 : e.val.2=f.val.1 ∨ e.val.2=f.val.2 := by
    have hmem : e.val.2∈({f.val.1,f.val.2} : Finset (Fin m)) := by rw [← he]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem
  have hel := e.property
  have hfl := f.property
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso; omega
  · exact Subtype.ext (Prod.ext h1 h2)
  · exfalso; omega
  · exfalso; omega

theorem exists_samplePair_rows {m : ℕ} (V : Finset (Fin m)) (hV : V.card=2) :
    ∃ e : SampleIndexPair m, V={e.val.1,e.val.2} := by
  obtain ⟨a,b,hab,hV⟩ := Finset.card_eq_two.mp hV
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨⟨(a,b),hlt⟩,hV⟩
  · exact ⟨⟨(b,a),hlt⟩,hV.trans (Finset.pair_comm _ _)⟩

theorem mem_rowCollisionIncident_iff {m : ℕ} (i : Fin m) (e : SampleIndexPair m) :
    e∈rowCollisionIncident i ↔ i∈({e.val.1,e.val.2} : Finset (Fin m)) := by
  simp only [rowCollisionIncident,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton,eq_comm]

theorem rowDoubletonMember_iff {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) :
    (HasRowDoubletonPattern z ∧ RowCollisionParticipant z i) ↔
      ∃ e∈rowCollisionIncident i,RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z := by
  constructor
  · rintro ⟨⟨V,hV,hz⟩,hi⟩
    have hiV := (hz.participant_iff (by omega) i).mp hi
    obtain ⟨e,rfl⟩ := exists_samplePair_rows V hV
    exact ⟨e,(mem_rowCollisionIncident_iff i e).mpr hiV,hz⟩
  · rintro ⟨e,he,hz⟩
    have hc : ({e.val.1,e.val.2} : Finset (Fin m)).card=2 := Finset.card_pair (ne_of_lt e.property)
    exact ⟨⟨_,hc,hz⟩,(hz.participant_iff (by omega) i).mpr ((mem_rowCollisionIncident_iff i e).mp he)⟩

theorem rowDoubletonPattern_pair_unique {m n : ℕ} (z : Fin m → Fin n)
    (e f : SampleIndexPair m)
    (he : RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z)
    (hf : RowClassPattern ({f.val.1,f.val.2} : Finset (Fin m)) z) : e=f := by
  apply samplePair_rows_injective
  change ({e.val.1,e.val.2} : Finset (Fin m))={f.val.1,f.val.2}
  have hec : ({e.val.1,e.val.2} : Finset (Fin m)).card=2 := Finset.card_pair (ne_of_lt e.property)
  have hfc : ({f.val.1,f.val.2} : Finset (Fin m)).card=2 := Finset.card_pair (ne_of_lt f.property)
  exact he.unique_class (by omega) hf (by omega)

/-- Exact uniqueness, not a union-bound relaxation, for single doubletons. -/
theorem rowDoubletonIncidence_eq_sum {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) :
    rowDoubletonIncidence z i=
      ∑ e∈rowCollisionIncident i,
        if RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z then (1:ℝ) else 0 := by
  classical
  by_cases h : HasRowDoubletonPattern z ∧ RowCollisionParticipant z i
  · obtain ⟨e,he,hz⟩ := (rowDoubletonMember_iff z i).mp h
    rw [rowDoubletonIncidence,if_pos h]
    symm
    rw [Finset.sum_eq_single e]
    · simp only [if_pos hz]
    · intro f hf hfe
      have hn : ¬RowClassPattern ({f.val.1,f.val.2} : Finset (Fin m)) z :=
        fun hfz => hfe (rowDoubletonPattern_pair_unique z f e hfz hz)
      simp only [if_neg hn]
    · exact fun hn => (hn he).elim
  · rw [rowDoubletonIncidence,if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have hn : ¬RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z :=
      fun hz => h ((rowDoubletonMember_iff z i).mpr ⟨e,he,hz⟩)
    simp only [if_neg hn]

theorem rowDoubletonParticipationMass_eq_sum {m n : ℕ} (X : Board m n) (i : Fin m) :
    rowDoubletonParticipationMass X i=
      ∑ e∈rowCollisionIncident i,rowDoubletonProbability X e := by
  classical
  unfold rowDoubletonParticipationMass
  simp_rw [rowDoubletonIncidence_eq_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  unfold rowDoubletonProbability rowAssignmentEvent
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z <;> simp [h]

/-- The exact normalized single-doubleton quantity used in the earlier
local collision bound. The identity even retains the zero denominator. -/
theorem rowDoubletonParticipationMass_div {m n : ℕ} (X : Board m n) (i : Fin m) :
    rowDoubletonParticipationMass X i/rowAvoidance X=rowLocalizedDoubletonLoad X i := by
  rw [rowDoubletonParticipationMass_eq_sum]
  simp only [rowLocalizedDoubletonLoad,Finset.sum_div]

end DittertRybin
