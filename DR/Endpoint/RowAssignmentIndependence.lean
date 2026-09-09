import DR.Endpoint.RowCollisions
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Exact product-law splitting on an arbitrary selected row set. This
supplies the nonneighbor independence needed by the finite local lemma;
no independence is asserted for collision events sharing a row. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Product weight for the row coordinates satisfying R. -/
def rowRestrictedMass {m n : ℕ} (X : Board m n) (R : Fin m → Prop)
    [DecidablePred R] (z : {i // R i} → Fin n) : ℝ :=
  ∏ i, X i.val (z i)

/-- Selected and complementary row weights factor exactly. -/
theorem rowAssignmentMass_split {m n : ℕ} (X : Board m n) (R : Fin m → Prop)
    [DecidablePred R] (z : Fin m → Fin n) :
    rowAssignmentMass X z =
      rowRestrictedMass X R (fun i => z i.val)*
        rowRestrictedMass X (fun i => ¬R i) (fun i => z i.val) := by
  exact (Fintype.prod_subtype_mul_prod_subtype R (fun i => X i (z i))).symm

/-- Weighted observables on complementary row sets factor, including signed weights. -/
theorem rowAssignment_sum_split {m n : ℕ} (X : Board m n) (R : Fin m → Prop)
    [DecidablePred R] (f : ({i // R i} → Fin n) → ℝ)
    (g : ({i // ¬R i} → Fin n) → ℝ) :
    (∑ z, rowAssignmentMass X z * f (fun i => z i.val) * g (fun i => z i.val)) =
      (∑ a, rowRestrictedMass X R a * f a)*
        (∑ b, rowRestrictedMass X (fun i => ¬R i) b * g b) := by
  classical
  calc
    _ = ∑ q : ({i // R i} → Fin n) × ({i // ¬R i} → Fin n),
        (rowRestrictedMass X R q.1*rowRestrictedMass X (fun i => ¬R i) q.2)*f q.1*g q.2 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd R (fun _ => Fin n))
      intro z
      rw [rowAssignmentMass_split X R z]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Every selected row law is normalized when each actual row is normalized. -/
theorem sum_rowRestrictedMass {m n : ℕ} (X : Board m n) (R : Fin m → Prop)
    [DecidablePred R] (hs : ∀ i, rowSum X i = 1) :
    (∑ z, rowRestrictedMass X R z) = 1 := by
  classical
  unfold rowRestrictedMass
  rw [← Fintype.prod_sum]
  change (∏ i : {i // R i}, rowSum X i.val) = 1
  simp only [hs,Finset.prod_const_one]

/-- Integrating the unused rows preserves a selected-row observable. -/
theorem rowAssignment_sum_restrict {m n : ℕ} (X : Board m n) (R : Fin m → Prop)
    [DecidablePred R] (hs : ∀ i, rowSum X i = 1)
    (f : ({i // R i} → Fin n) → ℝ) :
    (∑ z, rowAssignmentMass X z * f (fun i => z i.val)) =
      ∑ a, rowRestrictedMass X R a * f a := by
  have h := rowAssignment_sum_split X R f (fun _ => 1)
  simpa only [mul_one,sum_rowRestrictedMass X _ hs] using h

/-- Events on complementary row coordinates are genuinely independent. -/
theorem rowAssignmentEvent_independent_complement {m n : ℕ} (X : Board m n)
    (R : Fin m → Prop) [DecidablePred R] (hs : ∀ i, rowSum X i = 1)
    (A : Set ({i // R i} → Fin n)) (B : Set ({i // ¬R i} → Fin n)) :
    rowAssignmentEvent X {z | (fun i => z i.val) ∈ A ∧ (fun i => z i.val) ∈ B} =
      rowAssignmentEvent X {z | (fun i => z i.val) ∈ A}*
        rowAssignmentEvent X {z | (fun i => z i.val) ∈ B} := by
  classical
  let f : ({i // R i} → Fin n) → ℝ := fun a => if a ∈ A then 1 else 0
  let g : ({i // ¬R i} → Fin n) → ℝ := fun b => if b ∈ B then 1 else 0
  have hjoint := rowAssignment_sum_split X R f g
  have hA := rowAssignment_sum_restrict X R hs f
  have hB := rowAssignment_sum_restrict X (fun i => ¬R i) hs g
  rw [← hA,← hB] at hjoint
  have hf : (∑ z, rowAssignmentMass X z*f (fun i => z i.val)) =
      rowAssignmentEvent X {z | (fun i => z i.val) ∈ A} := by
    unfold rowAssignmentEvent
    apply Finset.sum_congr rfl
    intro z hz
    by_cases ha : (fun i => z i.val) ∈ A <;> simp [f,ha]
  have hg : (∑ z, rowAssignmentMass X z*g (fun i => z i.val)) =
      rowAssignmentEvent X {z | (fun i => z i.val) ∈ B} := by
    unfold rowAssignmentEvent
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hb : (fun i => z i.val) ∈ B <;> simp [g,hb]
  rw [hf,hg] at hjoint
  rw [← hjoint]
  unfold rowAssignmentEvent
  apply Finset.sum_congr rfl
  intro z hz
  by_cases ha : (fun i => z i.val) ∈ A <;>
    by_cases hb : (fun i => z i.val) ∈ B <;> simp [f,g,ha,hb]

/-- Avoid every edge in a finite family of row-collision pairs. -/
def AvoidRowCollisionPairs {m n : ℕ} (J : Finset (Fin m × Fin m))
    (z : Fin m → Fin n) : Prop := ∀ e ∈ J, z e.1 ≠ z e.2

/-- A collision edge is independent of joint avoidance of any family whose
endpoints all lie outside that edge. Shared-row events are not covered. -/
theorem rowCollision_independent_nonneighbors {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) (a b : Fin m) (J : Finset (Fin m × Fin m))
    (hJ : ∀ e ∈ J, e.1 ≠ a ∧ e.1 ≠ b ∧ e.2 ≠ a ∧ e.2 ≠ b) :
    rowAssignmentEvent X {z | z a=z b ∧ AvoidRowCollisionPairs J z} =
      rowCollisionProbability X a b * rowAssignmentEvent X {z | AvoidRowCollisionPairs J z} := by
  classical
  let R : Fin m → Prop := fun i => i=a ∨ i=b
  have ha : R a := Or.inl rfl
  have hb : R b := Or.inr rfl
  have he1 (e : J) : ¬R e.val.1 := by
    have h := hJ e.val e.property
    simp only [R,not_or]
    exact ⟨h.1,h.2.1⟩
  have he2 (e : J) : ¬R e.val.2 := by
    have h := hJ e.val e.property
    simp only [R,not_or]
    exact ⟨h.2.2.1,h.2.2.2⟩
  let A : Set ({i // R i} → Fin n) := {z | z ⟨a,ha⟩=z ⟨b,hb⟩}
  let B : Set ({i // ¬R i} → Fin n) :=
    {z | ∀ e : J, z ⟨e.val.1,he1 e⟩ ≠ z ⟨e.val.2,he2 e⟩}
  have h := rowAssignmentEvent_independent_complement X R hs A B
  have hB (z : Fin m → Fin n) : ((fun i => z i.val) ∈ B) ↔ AvoidRowCollisionPairs J z := by
    change (∀ e : J, z e.val.1 ≠ z e.val.2) ↔ ∀ e ∈ J, z e.1 ≠ z e.2
    exact Subtype.forall
  simpa only [A,Set.mem_ofPred_eq,hB,rowCollisionProbability] using h

end DittertRybin
