import DR.Endpoint.RowDeletionExpectation

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

private def X : Board 3 1 := fun i _ => (![2,3,5] : Fin 3 → ℝ) i
private theorem ht : RowClassPattern (Finset.univ : Finset (Fin 3)) (fun _ : Fin 3 => (0:Fin 1)) := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel

-- These row weights have total assignment mass thirty. Participation is
-- a mass in the unnormalized theorem, not silently a probability.
example (i : Fin 3) : rowDeficitTwoParticipationMass X i=30 := by
  unfold rowDeficitTwoParticipationMass
  rw [Fintype.sum_unique]
  change rowAssignmentMass X (fun _ => 0)*rowDeficitTwoIncidence (fun _ => 0) i=30
  rw [rowDeficitTwoIncidence_of_triple ht (by decide)]
  norm_num [rowAssignmentMass,X,Fin.prod_univ_succ,rowClassIncidence]

example (i : Fin 3) : rowDoubletonParticipationMass X i=0 := by
  unfold rowDoubletonParticipationMass
  rw [Fintype.sum_unique]
  have hn : ¬HasRowDoubletonPattern (fun _ : Fin 3 => (0:Fin 1)) := by
    intro h
    exact rowDoubleton_not_deficitTwo h (Or.inl ⟨_,by decide,ht⟩)
  change rowAssignmentMass X (fun _ => 0)*rowDoubletonIncidence (fun _ => 0) i=0
  simp [rowDoubletonIncidence,hn]

example : rowDeletionExpectation X 0 1=30 := by
  unfold rowDeletionExpectation
  rw [Fintype.sum_unique]
  change rowAssignmentMass X (fun _ => 0)*rowDeletionMatrix (fun _ => 0) 0 1=30
  rw [ht.deletionMatrix_triple (by decide)]
  norm_num [rowAssignmentMass,X,Fin.prod_univ_succ]

-- The zero diagonal survives averaging.
example {m n : ℕ} (P : Board m n) (i : Fin m) : rowDeletionExpectation P i i=0 := by
  simp [rowDeletionExpectation,rowDeletionMatrix_self]

-- All equalities used to assemble the expectation are valid for signed
-- weights too; nonnegativity is required only for its inequality.
example (P : Board 3 2) (x : Fin 3 → ℝ) :
    quadraticValue (rowDeletionExpectation P) x=
      ∑ z : Fin 3 → Fin 2,rowAssignmentMass P z*quadraticValue (rowDeletionMatrix z) x :=
  quadraticValue_rowDeletionExpectation P x

example (P : Board 0 0) (x : Fin 0 → ℝ) :
    rowAvoidance P*((∑ i,x i^2)-(∑ i,x i)^2)+
      (∑ i,rowDoubletonParticipationMass P i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowDoubletonParticipationMass P i*x i)-
      2*(∑ i,rowDeficitTwoParticipationMass P i*x i^2) ≤
        -quadraticValue (rowDeletionExpectation P) x :=
  rowDeletion_expectation_lower P (fun i => Fin.elim0 i) x

#print axioms quadraticValue_rowDeletionExpectation
#print axioms rowAssignment_sum_incidence
#print axioms rowAssignment_injective_indicator
#print axioms rowDeletion_expectation_lower

end DittertRybin.Tests
