import DR.Endpoint.RowCollisionClasses

/-! Literal two-class collision patterns. The unconditioned equalities in
disjoint row sets factor under the actual independent row law; all other
collision edges are forbidden only in the exact-pattern numerator. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Equalities within disjoint classes are independent, even for signed
normalized row weights. No prohibition on their common column labels is imposed here. -/
theorem rowClassEvent_independent {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (V W : Finset (Fin m)) (hVW : Disjoint V W) :
    rowAssignmentEvent X {z | RowClassEvent V z ∧ RowClassEvent W z} =
      rowAssignmentEvent X {z | RowClassEvent V z}*rowAssignmentEvent X {z | RowClassEvent W z} := by
  classical
  have hw (i : W) : i.val ∉ V := fun hi => Finset.disjoint_left.mp hVW hi i.property
  let A : Set ({i // i ∈ V} → Fin n) := {z | ∀ i h, z i=z h}
  let C : Set ({i // i ∉ V} → Fin n) :=
    {z | ∀ i h : W, z ⟨i.val,hw i⟩=z ⟨h.val,hw h⟩}
  have h := rowAssignmentEvent_independent_complement X (fun i => i ∈ V) hs A C
  have hA (z : Fin m → Fin n) : ((fun i => z i.val) ∈ A) ↔ RowClassEvent V z := by
    simp only [A,Set.mem_ofPred_eq,RowClassEvent,Subtype.forall]
  have hC (z : Fin m → Fin n) : ((fun i => z i.val) ∈ C) ↔ RowClassEvent W z := by
    simp only [C,Set.mem_ofPred_eq,RowClassEvent,Subtype.forall]
  simpa only [hA,hC] using h

/-- The prescribed two classes occur and every other row collision is absent. -/
def RowTwoClassPattern {m n : ℕ} (V W : Finset (Fin m)) (z : Fin m → Fin n) : Prop :=
  (RowClassEvent V z ∧ RowClassEvent W z) ∧
    ∀ e ∈ Finset.univ \ (rowClassEdges V ∪ rowClassEdges W), ¬RowCollisionEvent e z

/-- The exact two-class pattern has the expected selected-row ratio bound. -/
theorem rowTwoClassPattern_ratio_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (V W : Finset (Fin m)) (hVW : Disjoint V W) :
    rowAssignmentEvent X {z | RowTwoClassPattern V W z}/rowAvoidance X ≤
      (4/3:ℝ)^(V ∪ W).card*
        (rowAssignmentEvent X {z | RowClassEvent V z}*rowAssignmentEvent X {z | RowClassEvent W z}) := by
  classical
  let A : Set ({i // i ∈ V ∪ W} → Fin n) := {z |
    (∀ i h : V, z ⟨i.val,Finset.mem_union_left W i.property⟩=z ⟨h.val,Finset.mem_union_left W h.property⟩) ∧
    (∀ i h : W, z ⟨i.val,Finset.mem_union_right V i.property⟩=z ⟨h.val,Finset.mem_union_right V h.property⟩)}
  have hA (z : Fin m → Fin n) : RowSelectedEvent (V ∪ W) A z ↔ RowClassEvent V z ∧ RowClassEvent W z := by
    simp only [RowSelectedEvent,A,Set.mem_ofPred_eq,RowClassEvent,Subtype.forall]
  have hL : rowClassEdges V ∪ rowClassEdges W ⊆ rowCollisionTouch (V ∪ W) := by
    intro e he
    simp only [Finset.mem_union,rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
    simp only [rowCollisionTouch,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    tauto
  have h := rowSelectedEvent_removed_edges_ratio X hX hs hd (V ∪ W) A
    (rowClassEdges V ∪ rowClassEdges W) hL
  simpa only [hA,RowTwoClassPattern,rowClassEvent_independent X hs V W hVW] using h

theorem rowClassEvent_pair_mass {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (e : SampleIndexPair m) :
    rowAssignmentEvent X {z | RowClassEvent {e.val.1,e.val.2} z} =
      rowCollisionProbability X e.val.1 e.val.2 := by
  rw [rowClassEvent_mass X hs _ (by simp),rowCollisionProbability_eq X hs _ _ (ne_of_lt e.property)]
  simp [ne_of_lt e.property]

/-- Probability that precisely the two specified pairs are nonsingleton classes. -/
noncomputable def rowTwoDoubletonsProbability {m n : ℕ} (X : Board m n)
    (e f : SampleIndexPair m) : ℝ :=
  rowAssignmentEvent X {z | RowTwoClassPattern {e.val.1,e.val.2} {f.val.1,f.val.2} z}

/-- The actual two-doubleton ratio, with the exact 256/81 factor. -/
theorem rowTwoDoubletonsProbability_ratio_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (e f : SampleIndexPair m)
    (hdisj : Disjoint ({e.val.1,e.val.2} : Finset (Fin m)) {f.val.1,f.val.2}) :
    rowTwoDoubletonsProbability X e f/rowAvoidance X ≤
      (256/81)*(rowCollisionProbability X e.val.1 e.val.2*rowCollisionProbability X f.val.1 f.val.2) := by
  have h := rowTwoClassPattern_ratio_le X hX hs hd {e.val.1,e.val.2} {f.val.1,f.val.2} hdisj
  rw [rowClassEvent_pair_mass X hs e,rowClassEvent_pair_mass X hs f,
    Finset.card_union_of_disjoint hdisj] at h
  simpa [rowTwoDoubletonsProbability,ne_of_lt e.property,ne_of_lt f.property,
    show (4/3:ℝ)^4=256/81 by norm_num] using h

end DittertRybin
