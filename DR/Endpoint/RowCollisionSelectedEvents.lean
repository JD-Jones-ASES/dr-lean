import DR.Endpoint.RowCollisionLocalLemma
import DR.Endpoint.FinitePatternBound

/-! Events on an explicit selected set of rows are independent of joint
collision avoidance on its complement. Prescribed edges may be removed
from avoidance; the local lemma accounts for their product separately. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Edges touching at least one selected row. -/
def rowCollisionTouch {m : ℕ} (V : Finset (Fin m)) : Finset (SampleIndexPair m) :=
  Finset.univ.filter (fun e => e.val.1 ∈ V ∨ e.val.2 ∈ V)

/-- Pull back an actual event on the selected row coordinates. -/
def RowSelectedEvent {m n : ℕ} (V : Finset (Fin m))
    (A : Set ({i // i ∈ V} → Fin n)) (z : Fin m → Fin n) : Prop :=
  (fun i => z i.val) ∈ A

/-- The touching-edge load counts each edge once, while row loads may
count an internal edge twice. This gives the required inequality. -/
theorem rowCollisionTouch_load_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (V : Finset (Fin m)) :
    (∑ e ∈ rowCollisionTouch V, rowCollisionProbability X e.val.1 e.val.2) ≤
      ∑ i ∈ V, rowCollisionLoad X i := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [rowCollisionTouch]
  | @insert i V hi ih =>
    have he : rowCollisionTouch (insert i V) = rowCollisionIncident i ∪ rowCollisionTouch V := by
      ext e
      simp only [rowCollisionTouch,rowCollisionIncident,Finset.mem_filter,Finset.mem_univ,
        true_and,Finset.mem_insert,Finset.mem_union]
      tauto
    rw [he,Finset.sum_insert hi]
    have hu := Finset.sum_union_inter (s₁ := rowCollisionIncident i) (s₂ := rowCollisionTouch V)
      (f := fun e => rowCollisionProbability X e.val.1 e.val.2)
    have hn : 0 ≤ ∑ e ∈ rowCollisionIncident i ∩ rowCollisionTouch V,
        rowCollisionProbability X e.val.1 e.val.2 :=
      Finset.sum_nonneg (fun e _ => rowCollisionProbability_nonneg X hX _ _)
    rw [sum_rowCollisionIncident X i] at hu
    linarith

/-- A selected-row event is independent of joint avoidance of every family
of collision edges not touching those rows. No pairwise shortcut is used. -/
theorem rowSelectedEvent_independent_avoidance {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i=1) (V : Finset (Fin m))
    (A : Set ({i // i ∈ V} → Fin n)) (B : Finset (SampleIndexPair m))
    (hB : Disjoint B (rowCollisionTouch V)) :
    rowAssignmentEvent X {z | RowSelectedEvent V A z ∧ ∀ e ∈ B, ¬RowCollisionEvent e z} =
      rowAssignmentEvent X {z | RowSelectedEvent V A z}*
        rowAssignmentEvent X {z | ∀ e ∈ B, ¬RowCollisionEvent e z} := by
  classical
  have hends (e : B) : e.val.val.1 ∉ V ∧ e.val.val.2 ∉ V := by
    have h := Finset.disjoint_left.mp hB e.property
    simpa only [rowCollisionTouch,Finset.mem_filter,Finset.mem_univ,true_and,not_or] using h
  let C : Set ({i // i ∉ V} → Fin n) :=
    {z | ∀ e : B, z ⟨e.val.val.1,(hends e).1⟩ ≠ z ⟨e.val.val.2,(hends e).2⟩}
  have h := rowAssignmentEvent_independent_complement X (fun i => i ∈ V) hs A C
  have hC (z : Fin m → Fin n) : ((fun i => z i.val) ∈ C) ↔ ∀ e ∈ B, ¬RowCollisionEvent e z := by
    change (∀ e : B, z e.val.val.1 ≠ z e.val.val.2) ↔ ∀ e ∈ B, z e.val.1 ≠ z e.val.2
    exact Subtype.forall
  simpa only [hC,RowSelectedEvent,Set.mem_ofPred_eq] using h

/-- The arbitrary-event conditional bound specialized to actual selected
row coordinates, with all probability denominators cleared. -/
theorem rowSelectedEvent_conditioned_bound {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (V : Finset (Fin m))
    (A : Set ({i // i ∈ V} → Fin n)) (S : Finset (SampleIndexPair m)) :
    rowAssignmentEvent X {z | RowSelectedEvent V A z ∧ ∀ e ∈ S, ¬RowCollisionEvent e z}*
      (∏ e ∈ S ∩ rowCollisionTouch V, (1-2*rowCollisionProbability X e.val.1 e.val.2)) ≤
        rowAssignmentEvent X {z | RowSelectedEvent V A z}*
          rowAssignmentEvent X {z | ∀ e ∈ S, ¬RowCollisionEvent e z} := by
  classical
  obtain ⟨hx,hlll⟩ := rowCollision_scaled_parameters X hX (1/8) 2 hd
    (by norm_num) (by norm_num) (by norm_num)
  have hmass : ∑ z, rowAssignmentMass X z=1 := by simp only [sum_rowAssignmentMass,hs,Finset.prod_const_one]
  have h := FiniteEvents.finite_local_lemma_event_bound Finset.univ (rowAssignmentMass X)
    RowCollisionEvent rowCollisionNeighbors (fun e => 2*rowCollisionProbability X e.val.1 e.val.2)
    (fun z _ => rowAssignmentMass_nonneg X hX z) hmass hx (rowCollision_joint_independence X hs)
    (by intro e; rw [rowCollisionEvent_mass]; exact hlll e) (RowSelectedEvent V A) (rowCollisionTouch V) S
    (by intro B hB; simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,
      FiniteEvents.avoidanceMass] using rowSelectedEvent_independent_avoidance X hs V A B hB)
  simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,FiniteEvents.avoidanceMass] using h

/-- Remove the prescribed edge set L from avoidance and restore its full
product in the denominator comparison. Internal collisions are retained. -/
theorem rowSelectedEvent_removed_edges_bound {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (V : Finset (Fin m))
    (A : Set ({i // i ∈ V} → Fin n)) (L : Finset (SampleIndexPair m))
    (hL : L ⊆ rowCollisionTouch V) :
    rowAssignmentEvent X {z | RowSelectedEvent V A z ∧ ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z}*
      (∏ e ∈ rowCollisionTouch V, (1-2*rowCollisionProbability X e.val.1 e.val.2)) ≤
        rowAssignmentEvent X {z | RowSelectedEvent V A z}*rowAvoidance X := by
  classical
  obtain ⟨hx,hlll⟩ := rowCollision_scaled_parameters X hX (1/8) 2 hd
    (by norm_num) (by norm_num) (by norm_num)
  have hmass : ∑ z, rowAssignmentMass X z=1 := by simp only [sum_rowAssignmentMass,hs,Finset.prod_const_one]
  have h := FiniteEvents.finite_local_lemma_removed_events_bound Finset.univ (rowAssignmentMass X)
    RowCollisionEvent rowCollisionNeighbors (fun e => 2*rowCollisionProbability X e.val.1 e.val.2)
    (fun z _ => rowAssignmentMass_nonneg X hX z) hmass hx (rowCollision_joint_independence X hs)
    (by intro e; rw [rowCollisionEvent_mass]; exact hlll e) (RowSelectedEvent V A)
    (rowCollisionTouch V) Finset.univ L (Finset.subset_univ L) hL
    (by intro B hB; simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,
      FiniteEvents.avoidanceMass] using rowSelectedEvent_independent_avoidance X hs V A B hB)
  have hall : FiniteEvents.avoidanceMass Finset.univ (rowAssignmentMass X) RowCollisionEvent Finset.univ =
      rowAvoidance X := by
    unfold FiniteEvents.avoidanceMass
    rw [rowAvoidance_eq_event,rowAssignmentEvent_eq_finiteMass]
    congr 1
    funext z
    simp only [Set.mem_ofPred_eq,Finset.mem_univ,forall_const,rowCollision_avoid_all_iff]
  rw [hall] at h
  simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,Finset.univ_inter] using h

end DittertRybin
