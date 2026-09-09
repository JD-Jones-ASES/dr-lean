import DR.Endpoint.RowDeletionPatterns

namespace DittertRybin.Tests
set_option backward.isDefEq.respectTransparency false

private def pairAssignment : Fin 5 → Fin 5 := ![0,0,1,2,3]
private def tripleAssignment : Fin 5 → Fin 5 := ![0,0,0,1,2]
private def twoPairsAssignment : Fin 5 → Fin 5 := ![0,0,1,1,2]
private def fourAssignment : Fin 5 → Fin 5 := ![0,0,0,0,1]

private theorem pair_pattern : RowClassPattern ({0,1} : Finset (Fin 5)) pairAssignment := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem triple_pattern : RowClassPattern ({0,1,2} : Finset (Fin 5)) tripleAssignment := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem twoPairs_pattern : RowTwoClassPattern ({0,1} : Finset (Fin 5)) {2,3} twoPairsAssignment := by
  unfold RowTwoClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem four_pattern : RowClassPattern ({0,1,2,3} : Finset (Fin 5)) fourAssignment := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel

-- An actual doubleton is repaired by hitting it, not by deleting two outsiders.
example : rowDeletionMatrix pairAssignment 0 2=1 := by
  rw [pair_pattern.deletionMatrix_pair (by decide)]
  norm_num
  all_goals decide +kernel
example : rowDeletionMatrix pairAssignment 2 3=0 := by
  rw [pair_pattern.deletionMatrix_pair (by decide)]
  norm_num
  all_goals decide +kernel
example : rowDeletionMatrix pairAssignment 0 1=1 := by
  rw [pair_pattern.deletionMatrix_pair (by decide)]
  norm_num

-- A tripleton gives exactly K3 on its three rows.
example : rowDeletionMatrix tripleAssignment 0 1=1 := by
  rw [triple_pattern.deletionMatrix_triple (by decide)]
  norm_num
example : rowDeletionMatrix tripleAssignment 0 3=0 := by
  rw [triple_pattern.deletionMatrix_triple (by decide)]
  norm_num
  all_goals decide +kernel

-- Two doubletons give K2,2 across the two classes, not within either class.
example : rowDeletionMatrix twoPairsAssignment 0 2=1 := by
  rw [twoPairs_pattern.deletionMatrix_two_pairs (by decide) (by decide) (by decide)]
  norm_num
  all_goals decide +kernel
example : rowDeletionMatrix twoPairsAssignment 0 1=0 := by
  rw [twoPairs_pattern.deletionMatrix_two_pairs (by decide) (by decide) (by decide)]
  norm_num
  all_goals decide +kernel
example : rowDeletionMatrix twoPairsAssignment 0 4=0 := by
  rw [twoPairs_pattern.deletionMatrix_two_pairs (by decide) (by decide) (by decide)]
  norm_num
  all_goals decide +kernel

-- A four-element class survives every two-row deletion with a collision.
example (a b : Fin 5) : rowDeletionMatrix fourAssignment a b=0 :=
  four_pattern.deletionMatrix_zero_of_large (by decide) a b

-- The zero diagonal is explicit, even on a completely injective assignment.
example : rowDeletionMatrix (fun i : Fin 5 => i) 0 0=0 := rowDeletionMatrix_self _ _
example : rowDeletionMatrix (fun i : Fin 5 => i) 0 1=1 := by
  have h := rowDeletionMatrix_of_injective (z := fun i : Fin 5 => i)
    (fun _ _ he => he) (0 : Fin 5) 1
  simpa only [if_neg (show (0:Fin 5) ≠ 1 by decide)] using h

-- Dropping the positive rank-one term changes the exact single-pair identity.
example : -rowDeletionMatrix pairAssignment 0 0 ≠
    rowClassIncidence ({0,1} : Finset (Fin 5)) 0-
      rowClassIncidence ({0,1} : Finset (Fin 5)) 0-rowClassIncidence ({0,1} : Finset (Fin 5)) 0 := by
  norm_num [rowDeletionMatrix_self,rowClassIncidence]

#print axioms RowClassPattern.eq_iff
#print axioms RowTwoClassPattern.eq_iff
#print axioms RowClassPattern.distinctOutside_iff
#print axioms RowTwoClassPattern.distinctOutside_iff
#print axioms RowClassPattern.deletionMatrix_pair
#print axioms RowClassPattern.deletionMatrix_triple
#print axioms RowTwoClassPattern.deletionMatrix_two_pairs
#print axioms RowClassPattern.neg_deletionMatrix_pair
#print axioms RowClassPattern.deletionMatrix_zero_of_large

end DittertRybin.Tests
