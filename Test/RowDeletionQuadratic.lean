import DR.Endpoint.RowDeletionQuadratic

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

private def pair : Fin 3 → Fin 2 := ![0,0,1]
private def triple : Fin 3 → Fin 1 := fun _ => 0
private def twoPairs : Fin 4 → Fin 2 := ![0,0,1,1]

private theorem hp : RowClassPattern ({0,1} : Finset (Fin 3)) pair := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem ht : RowClassPattern (Finset.univ : Finset (Fin 3)) triple := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem htw : RowTwoClassPattern ({0,1} : Finset (Fin 4)) {2,3} twoPairs := by
  unfold RowTwoClassPattern RowClassEvent RowCollisionEvent
  decide +kernel

-- Both deficit-two patterns attain the factor-two quadratic bound.
example : quadraticValue (rowDeletionMatrix triple) (fun _ => 1)=6 := by
  unfold quadraticValue
  simp_rw [ht.deletionMatrix_triple (by decide)]
  norm_num [Fin.sum_univ_succ,Fin.ext_iff,Fin.succ,-Fin.val_eq_zero_iff]

example : quadraticValue (rowDeletionMatrix twoPairs) (fun _ => 1)=8 := by
  unfold quadraticValue
  simp_rw [htw.deletionMatrix_two_pairs (by decide) (by decide) (by decide)]
  norm_num [Fin.sum_univ_succ,Fin.ext_iff,Fin.succ,-Fin.val_eq_zero_iff]

-- Replacing two by one is false already on the exact K3 assignment.
example : ¬(-1*(∑ _i : Fin 3, (1:ℝ)^2)≤
    -quadraticValue (rowDeletionMatrix triple) (fun _ => 1)) := by
  unfold quadraticValue
  simp_rw [ht.deletionMatrix_triple (by decide)]
  norm_num [Fin.sum_univ_succ,Fin.ext_iff,Fin.succ,-Fin.val_eq_zero_iff]

-- The omitted single-pair term is exactly a square, including mixed signs.
example : -quadraticValue (rowDeletionMatrix pair) (![1,-1,2] : Fin 3 → ℝ)=2 := by
  rw [hp.neg_deletion_quadratic_pair (by decide)]
  norm_num [Fin.sum_univ_succ,rowClassIncidence,Fin.ext_iff,Fin.succ,-Fin.val_eq_zero_iff]

-- General soundness accepts every real vector and does not require a
-- stochastic or positive total assignment weight.
example {m n : ℕ} {z : Fin m → Fin n} {V : Finset (Fin m)}
    (h : RowClassPattern V z) (hc : V.card=3) (x : Fin m → ℝ) :
    -2*(∑ i,rowClassIncidence V i*x i^2)≤-quadraticValue (rowDeletionMatrix z) x :=
  h.neg_deletion_quadratic_triple hc x

example (Q : Matrix (Fin 0) (Fin 0) ℝ) (x : Fin 0 → ℝ) :
    quadraticValue Q x≤∑ i,(∑ j,Q i j)*x i^2 :=
  quadraticValue_le_rowSums Q (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x

#print axioms quadraticValue_le_rowSums
#print axioms RowClassPattern.deletion_rowSum_triple
#print axioms RowTwoClassPattern.deletion_rowSum_two_pairs
#print axioms RowClassPattern.neg_deletion_quadratic_triple
#print axioms RowTwoClassPattern.neg_deletion_quadratic_two_pairs
#print axioms neg_deletion_quadratic_of_injective
#print axioms RowClassPattern.neg_deletion_quadratic_pair
#print axioms RowClassPattern.neg_deletion_quadratic_pair_lower

end DittertRybin.Tests
