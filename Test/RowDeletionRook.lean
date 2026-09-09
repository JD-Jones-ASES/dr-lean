import DR.Endpoint.RowDeletionRook
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private def P : Board 4 2 := ![![7,0],![0,11],![2,0],![0,3]]
private def S : Finset (Fin 4) := {0,1}
private theorem hc : (Finset.univ\S).card=2 := by decide +kernel
private def kept : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (fun i => ⟨i.val+2,by omega⟩) (by
    intro i j hij
    change i.val+2<j.val+2
    exact Nat.add_lt_add_right hij 2)

private theorem hkept : (Finset.univ\S).orderEmbOfFin hc=kept := by
  symm
  apply Finset.orderEmbOfFin_unique' hc
  intro i
  fin_cases i <;> decide +kernel

private theorem kept_board : (fun i j => P (kept i) j)=Matrix.diagonal ![(2:ℝ),3] := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hrook : rookSum (eraseRows P S) 2=6 := by
  rw [rookSum_eraseRows_endpoint P S hc,hkept,kept_board,rowAvoidance_square_eq_permanent]
  norm_num [Matrix.permanent_diagonal,Fin.prod_univ_two]

-- The actual two-rook sum has no extra factor 2!.
example : rookSum (eraseRows P S) 2=6 := hrook
example : rookSum (eraseRows P S) 2≠12 := by rw [hrook]; norm_num

private theorem hr (i : Fin 4) : rowSum P i≠0 := by
  fin_cases i <;> norm_num [P,rowSum,Fin.sum_univ_succ]

-- The two remaining normalized rows avoid collisions with probability one.
example : rowAssignmentEvent (normalizeRows P) {z | RowsDistinctOutside S z}=1 := by
  have h := rookSum_eraseRows_normalized P hr S hc
  have hp : (∏ i∈Finset.univ\S,rowSum P i)=6 := by
    have hs : Finset.univ\S=({2,3} : Finset (Fin 4)) := by decide +kernel
    rw [hs,Finset.prod_pair (by decide)]
    norm_num [P,rowSum,Fin.sum_univ_succ]
    change ((2:ℝ)+0)*(0+3)=6
    norm_num
  rw [hrook,hp] at h
  linarith

-- The full four-row avoidance event has probability zero on two columns.
-- Replacing the deleted-row event above by this event would be incorrect.
example : rowAvoidance (normalizeRows P)=0 := by
  let : IsEmpty (Fin 4 ↪ Fin 2) := ⟨fun e => by
    have h := Fintype.card_le_of_injective e e.injective
    norm_num at h⟩
  simp [rowAvoidance]

-- The empty remaining assignment keeps weight one, even on a zero board.
example : rookSum (eraseRows (0 : Board 2 0) Finset.univ) 0=1 := by
  rw [rookSum_eraseRows_endpoint (0 : Board 2 0) Finset.univ (by simp)]
  simp [rowAvoidance,rowAssignmentMass]

-- Signed nonzero row masses are valid in the exact normalization identity.
example (Q : Board 4 2) (hQ : ∀ i,rowSum Q i≠0) :
    rookSum (eraseRows Q S) 2=(∏ i∈Finset.univ\S,rowSum Q i)*
      rowAssignmentEvent (normalizeRows Q) {z | RowsDistinctOutside S z} :=
  rookSum_eraseRows_normalized Q hQ S hc

#print axioms rookSum_eraseRows_endpoint
#print axioms rowAssignmentEvent_distinctOutside
#print axioms rookSum_eraseRows_normalized

end DittertRybin.Tests
