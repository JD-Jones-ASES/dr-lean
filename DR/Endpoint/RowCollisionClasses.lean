import DR.Endpoint.RowCollisionTouchProduct

/-! Literal one-class collision patterns under the independent row law.
The selected-coordinate probability is computed exactly, and every edge
outside the prescribed class is forbidden. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All rows in V choose the same column. Empty and singleton V are vacuous. -/
def RowClassEvent {m n : ℕ} (V : Finset (Fin m)) (z : Fin m → Fin n) : Prop :=
  ∀ i ∈ V, ∀ h ∈ V, z i=z h

/-- The collision edges internal to a prescribed class. -/
def rowClassEdges {m : ℕ} (V : Finset (Fin m)) : Finset (SampleIndexPair m) :=
  Finset.univ.filter (fun e => e.val.1 ∈ V ∧ e.val.2 ∈ V)

/-- V is the prescribed class and every other collision edge is absent. -/
def RowClassPattern {m n : ℕ} (V : Finset (Fin m)) (z : Fin m → Fin n) : Prop :=
  RowClassEvent V z ∧ ∀ e ∈ Finset.univ \ rowClassEdges V, ¬RowCollisionEvent e z

/-- Specifying one value on a selected row set has the exact marginal product. -/
theorem rowAssignmentEvent_selected_constant {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (V : Finset (Fin m)) (u : Fin n) :
    rowAssignmentEvent X {z | ∀ i ∈ V, z i=u} = ∏ i ∈ V, X i u := by
  classical
  rw [rowAssignmentEvent_coordinate_constraints X (fun i j => i ∈ V → j=u)]
  have hf (i : Fin m) : (∑ j, if i ∈ V → j=u then X i j else 0) =
      if i ∈ V then X i u else 1 := by
    by_cases hi : i ∈ V
    · simp [hi]
    · simp only [hi,false_implies,if_true,if_false]
      exact hs i
  simp_rw [hf]
  exact Finset.prod_ite_mem_eq V (fun i => X i u)

/-- A nonempty class has the exact common-column moment. Signed normalized
rows are permitted in this identity. -/
theorem rowClassEvent_mass {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (V : Finset (Fin m)) (hV : V.Nonempty) :
    rowAssignmentEvent X {z | RowClassEvent V z} = ∑ u, ∏ i ∈ V, X i u := by
  classical
  obtain ⟨a,ha⟩ := hV
  have he (z : Fin m → Fin n) (u : Fin n) : (∀ i ∈ V, z i=u) ↔ z a=u ∧ RowClassEvent V z := by
    constructor
    · intro h
      exact ⟨h a ha,fun i hi j hj => (h i hi).trans (h j hj).symm⟩
    · rintro ⟨hu,h⟩
      exact fun i hi => (h i hi a ha).trans hu
  calc
    _ = ∑ z, ∑ u, if ∀ i ∈ V, z i=u then rowAssignmentMass X z else 0 := by
      unfold rowAssignmentEvent
      apply Finset.sum_congr rfl
      intro z hz
      change (if RowClassEvent V z then rowAssignmentMass X z else 0) = _
      simp_rw [he]
      by_cases hc : RowClassEvent V z <;> simp [hc,eq_comm]
    _ = ∑ u, rowAssignmentEvent X {z | ∀ i ∈ V, z i=u} := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      unfold rowAssignmentEvent
      apply Finset.sum_congr rfl
      intro z hz
      by_cases he : ∀ i ∈ V, z i=u <;> simp [he]
    _ = _ := by simp_rw [rowAssignmentEvent_selected_constant X hs V]

/-- The exact one-class pattern obeys the selected-row relative estimate. -/
theorem rowClassPattern_ratio_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (V : Finset (Fin m)) (hV : V.Nonempty) :
    rowAssignmentEvent X {z | RowClassPattern V z}/rowAvoidance X ≤
      (4/3:ℝ)^V.card*(∑ u, ∏ i ∈ V, X i u) := by
  classical
  let A : Set ({i // i ∈ V} → Fin n) := {z | ∀ i h, z i=z h}
  have hA (z : Fin m → Fin n) : RowSelectedEvent V A z ↔ RowClassEvent V z := by
    simp only [RowSelectedEvent,A,Set.mem_ofPred_eq,RowClassEvent,Subtype.forall]
  have hL : rowClassEdges V ⊆ rowCollisionTouch V := by
    intro e he
    simp only [rowClassEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
    simp only [rowCollisionTouch,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl he.1
  have h := rowSelectedEvent_removed_edges_ratio X hX hs hd V A (rowClassEdges V) hL
  simpa only [hA,RowClassPattern,rowClassEvent_mass X hs V hV] using h

/-- Probability that the only nonsingleton column class is the specified pair. -/
noncomputable def rowDoubletonProbability {m n : ℕ} (X : Board m n) (e : SampleIndexPair m) : ℝ :=
  rowAssignmentEvent X {z | RowClassPattern {e.val.1,e.val.2} z}

/-- The actual doubleton ratio, with the exact 16/9 constant. -/
theorem rowDoubletonProbability_ratio_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (e : SampleIndexPair m) :
    rowDoubletonProbability X e/rowAvoidance X ≤ (16/9)*rowCollisionProbability X e.val.1 e.val.2 := by
  have hne := ne_of_lt e.property
  have h := rowClassPattern_ratio_le X hX hs hd {e.val.1,e.val.2} (by simp)
  rw [rowCollisionProbability_eq X hs _ _ hne]
  simpa [rowDoubletonProbability,hne,show (4/3:ℝ)^2=16/9 by norm_num] using h

/-- Probability that the only nonsingleton column class is the specified triple. -/
noncomputable def rowTripletonProbability {m n : ℕ} (X : Board m n) (a b c : Fin m) : ℝ :=
  rowAssignmentEvent X {z | RowClassPattern {a,b,c} z}

/-- The actual tripleton ratio, with the exact common-column third moment. -/
theorem rowTripletonProbability_ratio_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (a b c : Fin m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rowTripletonProbability X a b c/rowAvoidance X ≤ (64/27)*(∑ u, X a u*X b u*X c u) := by
  have h := rowClassPattern_ratio_le X hX hs hd {a,b,c} (by simp)
  simpa [rowTripletonProbability,hab,hac,hbc,mul_assoc,show (4/3:ℝ)^3=64/27 by norm_num] using h

end DittertRybin
