import DR.Endpoint.RowAssignmentIndependence
import DR.Endpoint.RowCollisionUnion
import DR.Endpoint.FiniteAvoidance
import DR.Collision.Witnesses

/-! The actual independent-row collision graph has one increasing pair per
edge. Neighbors share a row and exclude the edge itself. All identities
retain zero-probability edges. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The row-collision event associated with an unordered edge. -/
def RowCollisionEvent {m n : ℕ} (e : SampleIndexPair m) (z : Fin m → Fin n) : Prop :=
  z e.val.1 = z e.val.2

theorem rowCollisionEvent_mass {m n : ℕ} (X : Board m n) (e : SampleIndexPair m) :
    FiniteEvents.mass Finset.univ (rowAssignmentMass X) (RowCollisionEvent e) =
      rowCollisionProbability X e.val.1 e.val.2 := by
  unfold RowCollisionEvent
  exact (rowAssignmentEvent_eq_finiteMass X {z | z e.val.1=z e.val.2}).symm

/-- The total increasing-edge mass is the half-ordered collision intensity. -/
theorem rowCollisionIntensity_eq_sum_edges {m n : ℕ} (X : Board m n) :
    rowCollisionIntensity X =
      ∑ e : SampleIndexPair m, rowCollisionProbability X e.val.1 e.val.2 := by
  classical
  have h := Finset.sum_subtype (p := fun e : Fin m × Fin m => e.1 < e.2) (F := inferInstance)
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun e => e.1 < e.2))
    (by simp) (fun e => rowCollisionProbability X e.1 e.2)
  rw [Finset.sum_filter,Fintype.sum_prod_type] at h
  rw [rowCollisionIntensity_eq_sum_lt]
  exact h

/-- Edges incident with a specified row. -/
def rowCollisionIncident {m : ℕ} (i : Fin m) : Finset (SampleIndexPair m) :=
  Finset.univ.filter (fun e => e.val.1=i ∨ e.val.2=i)

/-- The dependency neighborhood contains the other edges sharing a row. -/
def rowCollisionNeighbors {m : ℕ} (e : SampleIndexPair m) : Finset (SampleIndexPair m) :=
  ((rowCollisionIncident e.val.1) ∪ (rowCollisionIncident e.val.2)).erase e

/-- An incident unordered edge has exactly one other endpoint. -/
def rowIncidentEdgeEquiv {m : ℕ} (i : Fin m) :
    {h : Fin m // h ≠ i} ≃ {e : SampleIndexPair m // e.val.1=i ∨ e.val.2=i} where
  toFun h := if hh : i < h.val then ⟨⟨(i,h.val),hh⟩,Or.inl rfl⟩
    else ⟨⟨(h.val,i),lt_of_le_of_ne (le_of_not_gt hh) h.property⟩,Or.inr rfl⟩
  invFun e := if he : e.val.val.1=i then
    ⟨e.val.val.2, by have := e.val.property; omega⟩ else
    ⟨e.val.val.1,he⟩
  left_inv h := by
    apply Subtype.ext
    by_cases hh : i < h.val
    · simp [hh]
    · simp [hh,h.property]
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rcases e.property with he | he
    · have hh : i < e.val.val.2 := by have := e.val.property; omega
      simp only [dif_pos he,dif_pos hh]
      exact Prod.ext he.symm rfl
    · have hn : e.val.val.1 ≠ i := by have := e.val.property; omega
      have hh : ¬i < e.val.val.1 := by have := e.val.property; omega
      simp only [dif_neg hn,dif_neg hh]
      exact Prod.ext rfl he.symm

/-- The incident-edge sum is exactly the collision load, with no factor two. -/
theorem sum_rowCollisionIncident {m n : ℕ} (X : Board m n) (i : Fin m) :
    (∑ e ∈ rowCollisionIncident i, rowCollisionProbability X e.val.1 e.val.2) =
      rowCollisionLoad X i := by
  classical
  have h := Fintype.sum_equiv (rowIncidentEdgeEquiv i)
    (fun h => rowCollisionProbability X i h.val)
    (fun e => rowCollisionProbability X e.val.val.1 e.val.val.2) (by
      intro h
      by_cases hh : i < h.val
      · simp [rowIncidentEdgeEquiv,hh]
      · simp [rowIncidentEdgeEquiv,hh,rowCollisionProbability_symm X i h.val])
  have hleft : (∑ h : {h : Fin m // h ≠ i}, rowCollisionProbability X i h.val) =
      rowCollisionLoad X i := by
    exact (Finset.sum_subtype (Finset.univ.erase i) (by simp)
      (fun h => rowCollisionProbability X i h)).symm
  have hright : (∑ e : {e : SampleIndexPair m // e.val.1=i ∨ e.val.2=i},
      rowCollisionProbability X e.val.val.1 e.val.val.2) =
      ∑ e ∈ rowCollisionIncident i, rowCollisionProbability X e.val.1 e.val.2 := by
    exact (Finset.sum_subtype (rowCollisionIncident i) (by simp [rowCollisionIncident])
      (fun e => rowCollisionProbability X e.val.1 e.val.2)).symm
  rw [hleft,hright] at h
  exact h.symm

/-- A neighborhood is contained in the two endpoint stars. -/
theorem rowCollisionNeighbors_load_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (e : SampleIndexPair m) :
    (∑ f ∈ rowCollisionNeighbors e, rowCollisionProbability X f.val.1 f.val.2) ≤
      rowCollisionLoad X e.val.1 + rowCollisionLoad X e.val.2 := by
  classical
  rw [← sum_rowCollisionIncident X e.val.1,← sum_rowCollisionIncident X e.val.2]
  apply (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset e _) (fun f _ _ => rowCollisionProbability_nonneg X hX _ _)).trans
  have h := Finset.sum_union_inter (s₁ := rowCollisionIncident e.val.1)
    (s₂ := rowCollisionIncident e.val.2) (f := fun f => rowCollisionProbability X f.val.1 f.val.2)
  have hn : 0 ≤ ∑ f ∈ rowCollisionIncident e.val.1 ∩ rowCollisionIncident e.val.2,
      rowCollisionProbability X f.val.1 f.val.2 :=
    Finset.sum_nonneg (fun f _ => rowCollisionProbability_nonneg X hX _ _)
  linarith

/-- The probability of an edge is no greater than either endpoint load. -/
theorem rowCollisionProbability_le_load {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (e : SampleIndexPair m) :
    rowCollisionProbability X e.val.1 e.val.2 ≤ rowCollisionLoad X e.val.1 := by
  unfold rowCollisionLoad
  apply Finset.single_le_sum (f := fun h => rowCollisionProbability X e.val.1 h)
    (fun h _ => rowCollisionProbability_nonneg X hX _ _)
  simp [ne_of_gt e.property]

/-- Avoiding all unordered collision edges is exactly injectivity. -/
theorem rowCollision_avoid_all_iff {m n : ℕ} (z : Fin m → Fin n) :
    (∀ e : SampleIndexPair m, ¬RowCollisionEvent e z) ↔ Function.Injective z := by
  constructor
  · intro hz i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hz ⟨(i,j),hlt⟩ hij
    · exact hz ⟨(j,i),hlt⟩ hij.symm
  · intro hz e he
    exact (ne_of_lt e.property) (hz he)

/-- Actual joint nonneighbor independence, in the generic finite-mass API. -/
theorem rowCollision_joint_independence {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (e : SampleIndexPair m)
    (S : Finset (SampleIndexPair m)) (heS : e ∉ S)
    (hdisj : Disjoint S (rowCollisionNeighbors e)) :
    FiniteEvents.hitAvoidanceMass Finset.univ (rowAssignmentMass X) RowCollisionEvent e S =
      FiniteEvents.mass Finset.univ (rowAssignmentMass X) (RowCollisionEvent e)*
        FiniteEvents.avoidanceMass Finset.univ (rowAssignmentMass X) RowCollisionEvent S := by
  classical
  let J := S.image Subtype.val
  have hJ : ∀ f ∈ J, f.1 ≠ e.val.1 ∧ f.1 ≠ e.val.2 ∧ f.2 ≠ e.val.1 ∧ f.2 ≠ e.val.2 := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    have hge : g ≠ e := fun h => heS (h ▸ hg)
    have hn := Finset.disjoint_left.mp hdisj hg
    simp only [rowCollisionNeighbors,Finset.mem_erase,Finset.mem_union,
      rowCollisionIncident,Finset.mem_filter,Finset.mem_univ,true_and] at hn
    tauto
  have h := rowCollision_independent_nonneighbors X hs e.val.1 e.val.2 J hJ
  have hJiff (z : Fin m → Fin n) : AvoidRowCollisionPairs J z ↔
      ∀ f ∈ S, ¬RowCollisionEvent f z := by
    simp [AvoidRowCollisionPairs,J,RowCollisionEvent]
  simp_rw [rowAssignmentEvent_eq_finiteMass] at h
  unfold FiniteEvents.hitAvoidanceMass FiniteEvents.avoidanceMass RowCollisionEvent
  simpa only [hJiff,
    rowCollisionProbability,rowAssignmentEvent_eq_finiteMass,RowCollisionEvent,
    Set.mem_ofPred_eq] using h

end DittertRybin
