import DR.Endpoint.RowCollisionLocalLemma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

-- Each row has a private column of mass 15/16 and one shared column of mass 1/16.
private noncomputable def commonPrivate (m : ℕ) : Board m (m+1) :=
  fun i => Fin.cases (1/16) (fun h => if h=i then 15/16 else 0)

private theorem commonPrivate_nonneg (m : ℕ) (i : Fin m) (j : Fin (m+1)) :
    0 ≤ commonPrivate m i j := by
  refine Fin.cases ?_ (fun h => ?_) j
  · norm_num [commonPrivate]
  · by_cases hh : h=i <;> norm_num [commonPrivate,hh]

private theorem commonPrivate_sum (m : ℕ) (i : Fin m) : rowSum (commonPrivate m) i=1 := by
  simp [rowSum,commonPrivate,Fin.sum_univ_succ]
  norm_num

private theorem commonPrivate_collision (m : ℕ) (i h : Fin m) (hih : i ≠ h) :
    rowCollisionProbability (commonPrivate m) i h = 1/256 := by
  rw [rowCollisionProbability_eq _ (commonPrivate_sum m) i h hih,Fin.sum_univ_succ]
  have hz : ∀ a : Fin m,
      (if a=i then (15/16:ℝ) else 0)*(if a=h then (15/16:ℝ) else 0)=0 := by
    intro a
    by_cases ha : a=i
    · simp [ha,hih]
    · simp [ha]
  simp only [commonPrivate,Fin.cases_zero,Fin.cases_succ,hz,Finset.sum_const_zero]
  norm_num

private theorem commonPrivate_load (i : Fin 33) : rowCollisionLoad (commonPrivate 33) i=1/8 := by
  unfold rowCollisionLoad
  have he : (∑ h ∈ Finset.univ.erase i, rowCollisionProbability (commonPrivate 33) i h) =
      ∑ _h ∈ Finset.univ.erase i, (1/256:ℝ) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact commonPrivate_collision 33 i h (Finset.ne_of_mem_erase hh).symm
  rw [he]
  norm_num

-- This actual model has D=33/16>1, while every local load is exactly 1/8.
example : rowCollisionIntensity (commonPrivate 33) = 33/16 := by
  simp [rowCollisionIntensity,commonPrivate_load]
  norm_num
example : 1 < rowCollisionIntensity (commonPrivate 33) := by
  simp [rowCollisionIntensity,commonPrivate_load]
  norm_num
example : 0 < rowAvoidance (commonPrivate 33) := by
  apply rowAvoidance_pos_of_collisionLoad _ (commonPrivate_nonneg 33) (commonPrivate_sum 33)
  intro i
  exact (commonPrivate_load i).le
example (S : Finset (SampleIndexPair 33)) (e : SampleIndexPair 33) (he : e ∉ S) :
    rowAssignmentEvent (commonPrivate 33)
      {z | RowCollisionEvent e z ∧ ∀ f ∈ S, ¬RowCollisionEvent f z} ≤
      (1/128)*rowAssignmentEvent (commonPrivate 33) {z | ∀ f ∈ S, ¬RowCollisionEvent f z} := by
  have h := (rowCollision_local_lemma _ (commonPrivate_nonneg 33) (commonPrivate_sum 33)
    (fun i => (commonPrivate_load i).le) S).2 e he
  rw [commonPrivate_collision 33 _ _ (ne_of_lt e.property)] at h
  norm_num at h ⊢
  exact h

-- Zero event probabilities remain in the graph, including the all-zero parameter endpoint.
private def distinctRows : Board 2 2 := Matrix.diagonal (fun _ => 1)
private theorem distinctRows_nonneg (i j : Fin 2) : 0 ≤ distinctRows i j := by
  simp only [distinctRows,Matrix.diagonal_apply]
  split_ifs <;> norm_num
private theorem distinctRows_sum (i : Fin 2) : rowSum distinctRows i=1 := by
  simp [rowSum,distinctRows,Matrix.diagonal_apply]
private theorem distinctRows_load (i : Fin 2) : rowCollisionLoad distinctRows i=0 := by
  unfold rowCollisionLoad
  apply Finset.sum_eq_zero
  intro h hh
  have hih := (Finset.ne_of_mem_erase hh).symm
  rw [rowCollisionProbability_eq distinctRows distinctRows_sum i h hih]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hi : i=j
  · have hhj : h ≠ j := by simpa [hi] using hih.symm
    simp [distinctRows,hi,hhj]
  · simp [distinctRows,Matrix.diagonal_apply,hi]
example : 0 < rowAvoidance distinctRows :=
  rowAvoidance_pos_of_collisionLoad distinctRows distinctRows_nonneg distinctRows_sum
    (fun i => by rw [distinctRows_load]; norm_num)
example : (∏ e : SampleIndexPair 2,
    (1-rowCollisionProbability distinctRows e.val.1 e.val.2/(1-4*0))) ≤ rowAvoidance distinctRows :=
  rowAvoidance_lower_refinedProduct distinctRows distinctRows_nonneg distinctRows_sum
    0 (by norm_num) (by norm_num) (fun i => (distinctRows_load i).le)

-- Empty row sets are valid product laws and avoid every collision.
example : 0 < rowAvoidance (0 : Board 0 0) := by
  apply rowAvoidance_pos_of_collisionLoad
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

-- The scalar guard is sharp at d=1/8; increasing d makes this chosen parameter fail.
example : (1:ℝ) ≤ (1/(1-4*(1/8)))*(1-2*(1/(1-4*(1/8)))*(1/8)) := by norm_num
example : ¬(1:ℝ) ≤ (1/(1-4*(13/100)))*(1-2*(1/(1-4*(13/100)))*(13/100)) := by norm_num

#print axioms sum_rowCollisionIncident
#print axioms rowCollisionNeighbors_load_le
#print axioms rowCollisionIntensity_eq_sum_edges
#print axioms rowCollision_joint_independence
#print axioms rowCollision_local_lemma
#print axioms rowAvoidance_pos_of_collisionLoad
#print axioms rowAvoidance_lower_collisionProduct
#print axioms rowAvoidance_lower_refinedProduct

end DittertRybin.Tests
