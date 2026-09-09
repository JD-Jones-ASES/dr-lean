import DR.Endpoint.RowCollisionTwoClasses
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private noncomputable def tripleRows : Board 3 4 :=
  ![![(1/4:ℝ),3/4,0,0],![1/4,0,3/4,0],![1/4,0,0,3/4]]
private theorem tripleRows_nonneg (i : Fin 3) (j : Fin 4) : 0 ≤ tripleRows i j := by
  fin_cases i <;> fin_cases j <;> norm_num [tripleRows]
private theorem tripleRows_sum (i : Fin 3) : rowSum tripleRows i=1 := by
  fin_cases i <;> norm_num [rowSum,tripleRows,Fin.sum_univ_succ]
private theorem tripleRows_collision (i h : Fin 3) (hih : i ≠ h) :
    rowCollisionProbability tripleRows i h=1/16 := by
  rw [rowCollisionProbability_eq tripleRows tripleRows_sum i h hih]
  fin_cases i <;> fin_cases h
  all_goals simp at hih
  all_goals norm_num [tripleRows,Fin.sum_univ_succ]
private theorem tripleRows_load (i : Fin 3) : rowCollisionLoad tripleRows i ≤ 1/8 := by
  unfold rowCollisionLoad
  have hsum : (∑ h ∈ Finset.univ.erase i, rowCollisionProbability tripleRows i h) =
      ∑ _h ∈ Finset.univ.erase i, (1/16:ℝ) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact tripleRows_collision i h (Finset.ne_of_mem_erase hh).symm
  rw [hsum]
  norm_num

private theorem tripleRows_class_mass : rowAssignmentEvent tripleRows
    {z | RowClassEvent (Finset.univ : Finset (Fin 3)) z}=1/64 := by
  rw [rowClassEvent_mass tripleRows tripleRows_sum _ (by simp)]
  norm_num [tripleRows,Fin.sum_univ_succ,Fin.prod_univ_succ]

-- The literal exact tripleton is positive, with its exact third-moment mass.
example : rowTripletonProbability tripleRows 0 1 2=1/64 := by
  have hV : ({0,1,2} : Finset (Fin 3))=Finset.univ := by decide
  simpa only [rowTripletonProbability,hV,RowClassPattern,rowClassEdges,Finset.mem_univ,
    and_self,Finset.filter_true,Finset.sdiff_self,Finset.notMem_empty,false_implies,
    implies_true,and_true] using tripleRows_class_mass
example : rowTripletonProbability tripleRows 0 1 2/rowAvoidance tripleRows ≤ (64/27)*(1/64) := by
  have h := rowTripletonProbability_ratio_le tripleRows tripleRows_nonneg tripleRows_sum tripleRows_load
    0 1 2 (by decide) (by decide) (by decide)
  have hm : (∑ u, tripleRows 0 u*tripleRows 1 u*tripleRows 2 u)=(1/64:ℝ) := by
    norm_num [tripleRows,Fin.sum_univ_succ]
    change (1/16:ℝ)*(1/4)=1/64
    norm_num
  rw [hm] at h
  exact h

-- Overlapping pair classes fail the independence conclusion: 1/64 is not 1/256.
example : rowAssignmentEvent tripleRows {z | RowClassEvent ({0,1} : Finset (Fin 3)) z ∧ RowClassEvent {0,2} z} ≠
    rowAssignmentEvent tripleRows {z | RowClassEvent ({0,1} : Finset (Fin 3)) z}*
      rowAssignmentEvent tripleRows {z | RowClassEvent ({0,2} : Finset (Fin 3)) z} := by
  have he : {z : Fin 3 → Fin 4 | RowClassEvent ({0,1} : Finset (Fin 3)) z ∧ RowClassEvent {0,2} z} =
      {z | RowClassEvent Finset.univ z} := by
    ext z
    constructor
    · rintro ⟨h1,h2⟩
      have hz (i : Fin 3) : z i=z 0 := by
        fin_cases i
        · rfl
        · exact h1 1 (by simp) 0 (by simp)
        · exact h2 2 (by simp) 0 (by simp)
      exact fun i _ h _ => (hz i).trans (hz h).symm
    · intro h
      constructor <;> intro i hi j hj <;> exact h i (Finset.mem_univ i) j (Finset.mem_univ j)
  rw [he,tripleRows_class_mass,rowClassEvent_pair_mass tripleRows tripleRows_sum ⟨(0,1),by decide⟩,
    rowClassEvent_pair_mass tripleRows tripleRows_sum ⟨(0,2),by decide⟩,
    tripleRows_collision _ _ (by decide),tripleRows_collision _ _ (by decide)]
  norm_num

-- Empty selected classes must not use the nonempty common-column moment formula.
example : rowAssignmentEvent (0 : Board 0 2) {z | RowClassEvent ∅ z}=1 := by
  simp [RowClassEvent,rowAssignmentEvent_univ]
example : (∑ _u : Fin 2, ∏ i ∈ (∅ : Finset (Fin 0)), (0 : Board 0 2) i _u)=2 := by simp

-- The genuine two-doubleton event forbids cross-class edges and all further collisions.
example (X : Board 4 7) (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) :
    rowTwoDoubletonsProbability X ⟨(0,1),by decide⟩ ⟨(2,3),by decide⟩/rowAvoidance X ≤
      (256/81)*(rowCollisionProbability X 0 1*rowCollisionProbability X 2 3) := by
  exact rowTwoDoubletonsProbability_ratio_le X hX hs hd _ _ (by decide)

-- A repeated row pair cannot satisfy the required disjointness gate.
example : ¬Disjoint ({0,1} : Finset (Fin 4)) {1,2} := by decide

#print axioms rowAssignmentEvent_selected_constant
#print axioms rowClassEvent_mass
#print axioms rowClassPattern_ratio_le
#print axioms rowDoubletonProbability_ratio_le
#print axioms rowTripletonProbability_ratio_le
#print axioms rowClassEvent_independent
#print axioms rowTwoClassPattern_ratio_le
#print axioms rowTwoDoubletonsProbability_ratio_le

end DittertRybin.Tests
