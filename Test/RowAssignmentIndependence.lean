import DR.Endpoint.RowAssignmentIndependence

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

-- No positivity or common row distribution is needed for algebraic independence.
example (X : Board 4 7) (hs : ∀ i, rowSum X i=1) :
    rowAssignmentEvent X {z | z 0=z 1 ∧ AvoidRowCollisionPairs {(2,3)} z} =
      rowCollisionProbability X 0 1*
        rowAssignmentEvent X {z | AvoidRowCollisionPairs {(2,3)} z} := by
  apply rowCollision_independent_nonneighbors X hs
  intro e he
  simp only [Finset.mem_singleton] at he
  subst e
  decide

-- Empty and full selected-row sets are allowed in the exact signed split.
example (X : Board 0 0) (f : ({_i : Fin 0 // False} → Fin 0) → ℝ)
    (g : ({_i : Fin 0 // ¬False} → Fin 0) → ℝ) :
    (∑ z, rowAssignmentMass X z*f (fun i => z i.val)*g (fun i => z i.val)) =
      (∑ a, rowRestrictedMass X (fun _ => False) a*f a)*
        (∑ b, rowRestrictedMass X (fun _ => ¬False) b*g b) :=
  rowAssignment_sum_split X (fun _ => False) f g

private noncomputable def shared : Board 3 2 := ![![1,0],![1/2,1/2],![1,0]]
private theorem shared_sum (i : Fin 3) : rowSum shared i=1 := by
  fin_cases i <;> norm_num [shared,rowSum,Fin.sum_univ_two]

-- Edges sharing one row can fail independence: here E01 and E12 coincide.
private theorem shared_joint :
    rowAssignmentEvent shared {z | z 0=z 1 ∧ z 1≠z 2} = 0 := by
  classical
  unfold rowAssignmentEvent
  apply Finset.sum_eq_zero
  intro z hz
  by_cases he : z 0=z 1 ∧ z 1≠z 2
  · simp only [Set.mem_ofPred_eq,if_pos he]
    have h02 : z 0≠z 2 := by simpa only [he.1] using he.2
    by_cases h0 : z 0=0
    · have h2 : z 2=1 := by
        have hn : z 2≠0 := by intro h; exact h02 (h0.trans h.symm)
        exact Fin.ext (by have := (z 2).isLt; omega)
      simp [rowAssignmentMass,shared,Fin.prod_univ_succ,h2]
    · have hz0 : z 0=1 := Fin.ext (by have := (z 0).isLt; omega)
      simp [rowAssignmentMass,shared,Fin.prod_univ_succ,hz0]
  · simp [he]

private theorem shared_01 : rowCollisionProbability shared 0 1=1/2 := by
  rw [rowCollisionProbability_eq shared shared_sum 0 1 (by decide)]
  norm_num [shared,Fin.sum_univ_two]

private theorem shared_12 : rowCollisionProbability shared 1 2=1/2 := by
  rw [rowCollisionProbability_eq shared shared_sum 1 2 (by decide),Fin.sum_univ_two]
  change (1/2:ℝ)*1+(1/2)*0=1/2
  norm_num

example : rowAssignmentEvent shared {z | z 0=z 1 ∧ z 1≠z 2} ≠
    rowCollisionProbability shared 0 1*rowAssignmentEvent shared {z | z 1≠z 2} := by
  have hc := rowAssignmentEvent_compl shared {z | z (1:Fin 3)=z 2}
  change rowAssignmentEvent shared {z | z 1≠z 2} = _ at hc
  rw [show (∏ i, rowSum shared i)=1 by simp only [shared_sum,Finset.prod_const_one]] at hc
  change rowAssignmentEvent shared {z | z 1≠z 2} = 1-rowCollisionProbability shared 1 2 at hc
  rw [shared_joint,shared_01,hc,shared_12]
  norm_num

#print axioms rowAssignmentMass_split
#print axioms rowAssignment_sum_split
#print axioms rowAssignment_sum_restrict
#print axioms rowAssignmentEvent_independent_complement
#print axioms rowCollision_independent_nonneighbors

end DittertRybin.Tests
