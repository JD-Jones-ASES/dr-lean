import DR.Endpoint.RowCollisionTouchProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private noncomputable def sharedRows : Board 2 3 := ![![(1/4:ℝ),3/4,0],![1/4,0,3/4]]
private theorem sharedRows_nonneg (i : Fin 2) (j : Fin 3) : 0 ≤ sharedRows i j := by
  fin_cases i <;> fin_cases j <;> norm_num [sharedRows]
private theorem sharedRows_sum (i : Fin 2) : rowSum sharedRows i=1 := by
  fin_cases i <;> norm_num [sharedRows,rowSum,Fin.sum_univ_succ]
private theorem sharedRows_collision (i h : Fin 2) (hih : i ≠ h) :
    rowCollisionProbability sharedRows i h=1/16 := by
  rw [rowCollisionProbability_eq sharedRows sharedRows_sum i h hih]
  fin_cases i <;> fin_cases h
  all_goals simp at hih
  all_goals norm_num [sharedRows,Fin.sum_univ_succ]
private theorem sharedRows_load (i : Fin 2) : rowCollisionLoad sharedRows i ≤ 1/8 := by
  unfold rowCollisionLoad
  have hsum : (∑ h ∈ Finset.univ.erase i, rowCollisionProbability sharedRows i h) =
      ∑ _h ∈ Finset.univ.erase i, (1/16:ℝ) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact sharedRows_collision i h (Finset.ne_of_mem_erase hh).symm
  rw [hsum]
  norm_num

private def selectedEquality : Set ({i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} → Fin 3) :=
  {z | z ⟨0,Finset.mem_univ 0⟩=z ⟨1,Finset.mem_univ 1⟩}

-- The prescribed equality has strictly positive probability.
example : rowAssignmentEvent sharedRows {z | RowSelectedEvent Finset.univ selectedEquality z}=1/16 := by
  change rowCollisionProbability sharedRows 0 1=1/16
  exact sharedRows_collision 0 1 (by decide)

-- Removing the prescribed edge yields a real ratio bound with factor16/9.
example : rowAssignmentEvent sharedRows {z | RowSelectedEvent Finset.univ selectedEquality z}/
    rowAvoidance sharedRows ≤ (16/9)*rowAssignmentEvent sharedRows {z | RowSelectedEvent Finset.univ selectedEquality z} := by
  have h := rowSelectedEvent_removed_edges_ratio sharedRows sharedRows_nonneg sharedRows_sum sharedRows_load
    Finset.univ selectedEquality Finset.univ (by intro e he; simp [rowCollisionTouch])
  norm_num only [Finset.sdiff_self,Finset.notMem_empty,false_implies,forall_const,and_true,
    Finset.card_univ,Fintype.card_fin,show (4/3:ℝ)^2=16/9 by norm_num] at h
  simpa only [implies_true,and_true] using h

-- Keeping that edge in the avoidance family instead forces probability zero.
example : rowAssignmentEvent sharedRows {z | RowSelectedEvent Finset.univ selectedEquality z ∧
    ∀ e : SampleIndexPair 2, ¬RowCollisionEvent e z}=0 := by
  have hfalse (z : Fin 2 → Fin 3) : ¬(RowSelectedEvent Finset.univ selectedEquality z ∧
      ∀ e : SampleIndexPair 2, ¬RowCollisionEvent e z) := by
    rintro ⟨he,havoid⟩
    exact havoid ⟨(0,1),by decide⟩ he
  unfold rowAssignmentEvent
  apply Finset.sum_eq_zero
  intro z hz
  exact if_neg (hfalse z)

-- Internal edges contribute twice to row loads but once to the touching product.
example (X : Board 2 5) (hX : ∀ i j, 0 ≤ X i j) :
    (∑ e ∈ rowCollisionTouch (Finset.univ : Finset (Fin 2)), rowCollisionProbability X e.val.1 e.val.2) ≤
      rowCollisionLoad X 0+rowCollisionLoad X 1 := by
  simpa only [Fin.sum_univ_two] using rowCollisionTouch_load_le X hX Finset.univ

-- The closed chord includes both endpoints; its product bound permits zero parameters.
example : 4*(0:ℝ)*Real.log (3/4) ≤ Real.log (1-0) :=
  log_one_sub_chord_quarter 0 (by norm_num) (by norm_num)
example : 4*(1/4:ℝ)*Real.log (3/4) ≤ Real.log (1-1/4) :=
  log_one_sub_chord_quarter (1/4) (by norm_num) (by norm_num)
example : (3/4:ℝ)^2 ≤ ∏ e : Fin 3, (1-(![(0:ℝ),1/4,1/4] e)) := by
  apply product_one_sub_ge_three_quarters_pow Finset.univ _ 2
  · intro e he; fin_cases e <;> norm_num
  · norm_num [Fin.sum_univ_succ]
example : (3/4:ℝ)^0 ≤ ∏ _e : Fin 0, (1-(0:ℝ)) := by
  apply product_one_sub_ge_three_quarters_pow Finset.univ _ 0
  · intro e; exact Fin.elim0 e
  · simp

#print axioms rowCollisionTouch_load_le
#print axioms rowSelectedEvent_independent_avoidance
#print axioms rowSelectedEvent_conditioned_bound
#print axioms rowSelectedEvent_removed_edges_bound
#print axioms log_one_sub_chord_quarter
#print axioms product_one_sub_ge_three_quarters_pow
#print axioms rowCollisionTouch_product_lower
#print axioms rowSelectedEvent_removed_edges_ratio

end DittertRybin.Tests
