import DR.Endpoint.RowIncidenceLocalization

/-! Actual deficit-two participation is dominated by the earlier localized
tripleton and disjoint-doubleton sums. The first doubleton is oriented to
contain the specified row; no independence or row normalization is used. -/

namespace DittertRybin
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_samplePair_complement_triple {m : ℕ} (V : Finset (Fin m))
    (hV : V.card=3) (i : Fin m) (hi : i∈V) :
    ∃ e∈rowPairsOutside i,V={i,e.val.1,e.val.2} := by
  have hec : (V.erase i).card=2 := by rw [Finset.card_erase_of_mem hi,hV]
  obtain ⟨e,he⟩ := exists_samplePair_rows (V.erase i) hec
  have ha : e.val.1∈V.erase i := by rw [he]; simp
  have hb : e.val.2∈V.erase i := by rw [he]; simp
  have hmem : e∈rowPairsOutside i := by
    simp only [rowPairsOutside,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨(Finset.mem_erase.mp ha).1,(Finset.mem_erase.mp hb).1⟩
  refine ⟨e,hmem,?_⟩
  calc
    V=insert i (V.erase i) := (Finset.insert_erase hi).symm
    _ = _ := by rw [he]

theorem rowDeficitTwoMember_exists {m n : ℕ} (z : Fin m → Fin n) (i : Fin m)
    (h : HasRowDeficitTwoPattern z ∧ RowCollisionParticipant z i) :
    (∃ e∈rowPairsOutside i,RowClassPattern ({i,e.val.1,e.val.2} : Finset (Fin m)) z) ∨
      ∃ e∈rowCollisionIncident i,∃ f∈rowPairsDisjoint e,
        RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z := by
  obtain ⟨hpat,hi⟩ := h
  rcases hpat with ⟨V,hV,hz⟩ | ⟨V,W,hV,hW,hdisj,hz⟩
  · have hiV := (hz.participant_iff (by omega) i).mp hi
    obtain ⟨e,he,rfl⟩ := exists_samplePair_complement_triple V hV i hiV
    exact Or.inl ⟨e,he,hz⟩
  · have hiVW := (hz.participant_iff (by omega) (by omega) i).mp hi
    obtain ⟨e,rfl⟩ := exists_samplePair_rows V hV
    obtain ⟨f,rfl⟩ := exists_samplePair_rows W hW
    rcases Finset.mem_union.mp hiVW with hiV | hiW
    · refine Or.inr ⟨e,(mem_rowCollisionIncident_iff i e).mpr hiV,f,?_,hz⟩
      simpa only [rowPairsDisjoint,Finset.mem_filter,Finset.mem_univ,true_and] using hdisj
    · refine Or.inr ⟨f,(mem_rowCollisionIncident_iff i f).mpr hiW,e,?_,hz.swap⟩
      simpa only [rowPairsDisjoint,Finset.mem_filter,Finset.mem_univ,true_and] using hdisj.symm

theorem rowDeficitTwoIncidence_le_sum {m n : ℕ} (z : Fin m → Fin n) (i : Fin m) :
    rowDeficitTwoIncidence z i ≤
      (∑ e∈rowPairsOutside i,
        if RowClassPattern ({i,e.val.1,e.val.2} : Finset (Fin m)) z then (1:ℝ) else 0)+
      ∑ e∈rowCollisionIncident i,∑ f∈rowPairsDisjoint e,
        if RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z then (1:ℝ) else 0 := by
  classical
  have htn : 0≤∑ e∈rowPairsOutside i,
      if RowClassPattern ({i,e.val.1,e.val.2} : Finset (Fin m)) z then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun e _ => by split_ifs <;> norm_num)
  have hdn : 0≤∑ e∈rowCollisionIncident i,∑ f∈rowPairsDisjoint e,
      if RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun f _ => by split_ifs <;> norm_num))
  by_cases h : HasRowDeficitTwoPattern z ∧ RowCollisionParticipant z i
  · rw [rowDeficitTwoIncidence,if_pos h]
    rcases rowDeficitTwoMember_exists z i h with ⟨e,he,hz⟩ | ⟨e,he,f,hf,hz⟩
    · have ht := Finset.single_le_sum (f := fun e : SampleIndexPair m =>
        if RowClassPattern ({i,e.val.1,e.val.2} : Finset (Fin m)) z then (1:ℝ) else 0)
        (fun e _ => by split_ifs <;> norm_num) he
      rw [if_pos hz] at ht
      linarith
    · have hf' := Finset.single_le_sum (f := fun f : SampleIndexPair m =>
        if RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z then (1:ℝ) else 0)
        (fun f _ => by split_ifs <;> norm_num) hf
      have he' := Finset.single_le_sum (f := fun e : SampleIndexPair m =>
        ∑ f∈rowPairsDisjoint e,
          if RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z then (1:ℝ) else 0)
        (fun e _ => Finset.sum_nonneg (fun f _ => by split_ifs <;> norm_num)) he
      rw [if_pos hz] at hf'
      linarith
  · rw [rowDeficitTwoIncidence,if_neg h]
    exact add_nonneg htn hdn

theorem rowDeficitTwoParticipationMass_le_sum {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (i : Fin m) :
    rowDeficitTwoParticipationMass X i ≤
      (∑ e∈rowPairsOutside i,rowTripletonProbability X i e.val.1 e.val.2)+
      ∑ e∈rowCollisionIncident i,∑ f∈rowPairsDisjoint e,rowTwoDoubletonsProbability X e f := by
  classical
  have h := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (rowDeficitTwoIncidence_le_sum z i) (rowAssignmentMass_nonneg X hX z))
  change rowDeficitTwoParticipationMass X i≤_ at h
  apply h.trans_eq
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    unfold rowTripletonProbability rowAssignmentEvent
    apply Finset.sum_congr rfl
    intro z hz
    by_cases ht : RowClassPattern ({i,e.val.1,e.val.2} : Finset (Fin m)) z <;> simp [ht]
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    unfold rowTwoDoubletonsProbability rowAssignmentEvent
    apply Finset.sum_congr rfl
    intro z hz
    by_cases ht : RowTwoClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2} z <;> simp [ht]

/-- Division by the actual positive avoidance mass gives precisely the
localized upper bound needed in the matrix criterion. -/
theorem rowDeficitTwoParticipationMass_div_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (hp : 0<rowAvoidance X) (i : Fin m) :
    rowDeficitTwoParticipationMass X i/rowAvoidance X≤rowLocalizedDeficitTwoLoad X i := by
  have h := div_le_div_of_nonneg_right (rowDeficitTwoParticipationMass_le_sum X hX i) hp.le
  apply h.trans_eq
  simp only [rowLocalizedDeficitTwoLoad,rowLocalizedTripletonLoad,rowLocalizedTwoDoubletonsLoad,
    add_div,Finset.sum_div]

end DittertRybin
