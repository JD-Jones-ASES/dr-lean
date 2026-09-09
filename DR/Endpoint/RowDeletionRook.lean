import DR.Endpoint.RowAssignmentIndependence
import DR.Endpoint.RowDeletionPatterns

/-! Exact rook normalization after row deletion. The independent law
is normalizeRows of the board supplied here; applying the theorem to a
column-deleted board therefore uses its own normalized row law. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- At the endpoint of the remaining row set, only its canonical increasing
row embedding contributes to the erased-board rook sum. -/
theorem rookSum_eraseRows_endpoint {m n k : ℕ} (P : Board m n)
    (S : Finset (Fin m)) (hk : (Finset.univ\S).card=k) :
    rookSum (eraseRows P S) k=
      rowAvoidance (fun i j => P ((Finset.univ\S).orderEmbOfFin hk i) j) := by
  classical
  let T : Finset (Fin m) := Finset.univ\S
  let r : Fin k ↪o Fin m := T.orderEmbOfFin hk
  have hr (i : Fin k) : r i∉S := by
    have hi := T.orderEmbOfFin_mem hk i
    exact (Finset.mem_sdiff.mp hi).2
  unfold rookSum
  rw [Finset.sum_eq_single r]
  · unfold rowAvoidance rowAssignmentMass
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.prod_congr rfl
    intro i hi
    simp only [eraseRows,if_neg (hr i)]
    rfl
  · intro q hq hqr
    have hex : ∃ i,q i∈S := by
      by_contra hn
      have hmem (i : Fin k) : q i∈T := by
        simp only [T,Finset.mem_sdiff,Finset.mem_univ,true_and]
        exact fun hi => hn ⟨i,hi⟩
      have heq : q=r := Finset.orderEmbOfFin_unique' hk hmem
      exact hqr heq
    obtain ⟨i,hi⟩ := hex
    apply Finset.sum_eq_zero
    intro c hc
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [eraseRows,if_pos hi]
  · exact fun h => (h (Finset.mem_univ r)).elim

/-- Integrating unused normalized rows turns the actual outside-distinctness
event into one independent column choice for every remaining row. -/
theorem rowAssignmentEvent_distinctOutside {m n k : ℕ} (X : Board m n)
    (hs : ∀ i,rowSum X i=1) (S : Finset (Fin m)) (hk : (Finset.univ\S).card=k) :
    rowAssignmentEvent X {z | RowsDistinctOutside S z}=
      rowAvoidance (fun i j => X ((Finset.univ\S).orderEmbOfFin hk i) j) := by
  classical
  let T : Finset (Fin m) := Finset.univ\S
  let : Fintype T := Subtype.fintype (fun i : Fin m => i∈T)
  let er : Fin k ≃ T := (T.orderIsoOfFin hk).toEquiv
  let f : (T → Fin n) → ℝ := fun a => if Function.Injective a then 1 else 0
  have hinj (z : Fin m → Fin n) : Function.Injective (fun i : T => z i.val) ↔ RowsDistinctOutside S z := by
    constructor
    · intro h i hi j hj he
      have hiT : i∈T := by simp [T,hi]
      have hjT : j∈T := by simp [T,hj]
      exact congrArg Subtype.val (h (a₁ := ⟨i,hiT⟩) (a₂ := ⟨j,hjT⟩) he)
    · intro h i j he
      exact Subtype.ext (h i.val (Finset.mem_sdiff.mp i.property).2 j.val (Finset.mem_sdiff.mp j.property).2 he)
  have h := rowAssignment_sum_restrict X (fun i => i∈T) hs f
  have hevent : rowAssignmentEvent X {z | RowsDistinctOutside S z}=
      ∑ z,rowAssignmentMass X z*f (fun i => z i.val) := by
    unfold rowAssignmentEvent
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hd : RowsDistinctOutside S z <;> simp [f,hinj z,hd]
  rw [hevent,h,rowAvoidance_eq_event]
  unfold rowAssignmentEvent
  apply Fintype.sum_equiv (Equiv.arrowCongr er.symm (Equiv.refl (Fin n)))
  intro a
  have hae : (Equiv.arrowCongr er.symm (Equiv.refl (Fin n))) a=(fun i => a (er i)) := rfl
  rw [hae]
  simp only [Set.mem_ofPred_eq]
  have hi : Function.Injective a ↔ Function.Injective (fun i => a (er i)) := by
    constructor
    · exact fun ha => ha.comp er.injective
    · intro ha i j he
      obtain ⟨i,rfl⟩ := er.surjective i
      obtain ⟨j,rfl⟩ := er.surjective j
      exact congrArg er (ha he)
  have hm : rowRestrictedMass X (fun i => i∈T) a=
      rowAssignmentMass (fun i j => X ((Finset.univ\S).orderEmbOfFin hk i) j) (fun i => a (er i)) := by
    exact (Equiv.prod_comp er (fun i : T => X i.val (a i))).symm
  by_cases ha : Function.Injective a <;> simp [f,← hi,ha,hm]

/-- The erased endpoint rook sum has no factorial. It is the product of
the remaining row masses times the actual avoidance event under the
board's normalized row law. -/
theorem rookSum_eraseRows_normalized {m n k : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) (S : Finset (Fin m)) (hk : (Finset.univ\S).card=k) :
    rookSum (eraseRows P S) k=
      (∏ i∈Finset.univ\S,rowSum P i)*
        rowAssignmentEvent (normalizeRows P) {z | RowsDistinctOutside S z} := by
  classical
  let T : Finset (Fin m) := Finset.univ\S
  let r : Fin k ↪o Fin m := T.orderEmbOfFin hk
  let Q : Board k n := fun i j => P (r i) j
  have hQ (i : Fin k) : rowSum Q i=rowSum P (r i) := rfl
  have hnQ : normalizeRows Q=(fun i j => normalizeRows P (r i) j) := rfl
  rw [rookSum_eraseRows_endpoint P S hk]
  change rowAvoidance Q=(_)*_
  rw [← rookSum_endpoint_eq_rowAvoidance Q,rookSum_endpoint_normalized Q (fun i => by rw [hQ]; exact hr _)]
  have he : (∏ i,rowSum Q i)=∏ i∈T,rowSum P i := by
    simp_rw [hQ]
    exact (Equiv.prod_comp (T.orderIsoOfFin hk).toEquiv (fun i : T => rowSum P i.val)).trans
      (Finset.prod_coe_sort T (rowSum P))
  rw [he,hnQ]
  congr 1
  exact (rowAssignmentEvent_distinctOutside (normalizeRows P) (normalizeRows_rowSum P hr) S hk).symm

end DittertRybin
