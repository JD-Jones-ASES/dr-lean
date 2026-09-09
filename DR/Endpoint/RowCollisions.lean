import DR.Endpoint.RowProduct
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Collision probabilities under independent, non-identically distributed
row assignments. Every event refers to the actual product law; normalization
is row by row. The algebraic identities permit signed row weights. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Coordinatewise constraints factor under the actual independent row law. -/
theorem rowAssignmentEvent_coordinate_constraints {m n : ℕ} (X : Board m n)
    (C : Fin m → Fin n → Prop) [∀ i, DecidablePred (C i)] :
    rowAssignmentEvent X {z | ∀ i, C i (z i)} =
      ∏ i, ∑ j, if C i j then X i j else 0 := by
  classical
  rw [Fintype.prod_sum]
  simp only [Fintype.prod_ite_zero, rowAssignmentEvent, rowAssignmentMass,
    Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hc : ∀ i, C i (z i) <;> simp [hc]

/-- Distinct rows have their two literal marginals, without an iid hypothesis. -/
theorem rowAssignmentEvent_two_coordinates {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) (i h : Fin m) (hih : i ≠ h) (u v : Fin n) :
    rowAssignmentEvent X {z | z i = u ∧ z h = v} = X i u * X h v := by
  classical
  have he : {z : Fin m → Fin n | z i = u ∧ z h = v} =
      {z | ∀ a, (a=i → z a=u) ∧ (a=h → z a=v)} := by
    ext z
    simp only [Set.mem_ofPred_eq, forall_and, forall_eq]
  rw [he,rowAssignmentEvent_coordinate_constraints X (fun a j => (a=i → j=u) ∧ (a=h → j=v))]
  have hf (a : Fin m) :
      (∑ j, if (a=i → j=u) ∧ (a=h → j=v) then X a j else 0) =
      (if a=i then X i u else 1)*(if a=h then X h v else 1) := by
    by_cases hai : a=i
    · subst a
      simp [hih]
    · by_cases hah : a=h
      · subst a
        simp [hih.symm]
      · simp only [hai,hah,false_implies,and_self,if_true,if_false,one_mul]
        change rowSum X a = 1
        exact hs a
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp

/-- Probability that the choices in rows i and h agree. -/
noncomputable def rowCollisionProbability {m n : ℕ} (X : Board m n) (i h : Fin m) : ℝ :=
  rowAssignmentEvent X {z | z i = z h}

/-- The actual collision event has the familiar marginal inner product. -/
theorem rowCollisionProbability_eq {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) (i h : Fin m) (hih : i ≠ h) :
    rowCollisionProbability X i h = ∑ j, X i j * X h j := by
  classical
  have he (z : Fin m → Fin n) :
      (if z i = z h then rowAssignmentMass X z else 0) =
        ∑ j, if z i=j ∧ z h=j then rowAssignmentMass X z else 0 := by
    simp only [ite_and]
    simp [eq_comm]
  unfold rowCollisionProbability rowAssignmentEvent
  calc
    _ = ∑ z, ∑ j, if z i=j ∧ z h=j then rowAssignmentMass X z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := he z
      by_cases hc : z i=z h
      · simpa only [Set.mem_ofPred_eq,if_pos hc] using hz'
      · simpa only [Set.mem_ofPred_eq,if_neg hc] using hz'
    _ = ∑ j, ∑ z, if z i=j ∧ z h=j then rowAssignmentMass X z else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := rowAssignmentEvent_two_coordinates X hs i h hih j j
      unfold rowAssignmentEvent at hj'
      calc
        _ = _ := ?_
        _ = _ := hj'
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hc : z i=j ∧ z h=j <;> simp [hc]

/-- The diagonal event is certain; it is excluded from every collision graph edge. -/
theorem rowCollisionProbability_self {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) (i : Fin m) : rowCollisionProbability X i i = 1 := by
  simp [rowCollisionProbability,rowAssignmentEvent_univ,hs]

theorem rowCollisionProbability_nonneg {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (i h : Fin m) : 0 ≤ rowCollisionProbability X i h :=
  rowAssignmentEvent_nonneg X hX _

theorem rowCollisionProbability_symm {m n : ℕ} (X : Board m n) (i h : Fin m) :
    rowCollisionProbability X i h = rowCollisionProbability X h i := by
  unfold rowCollisionProbability
  congr 1
  ext z
  exact eq_comm

/-- Sum of collision probabilities incident to one row. -/
noncomputable def rowCollisionLoad {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ h ∈ Finset.univ.erase i, rowCollisionProbability X i h

/-- Total unordered pair-collision mass, written as half the ordered sum. -/
noncomputable def rowCollisionIntensity {m n : ℕ} (X : Board m n) : ℝ :=
  (1/2)*∑ i, rowCollisionLoad X i

end DittertRybin
