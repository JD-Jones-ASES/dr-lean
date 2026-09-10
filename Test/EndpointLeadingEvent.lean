import DR.Endpoint.LeadingEvent
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- Omitting the ordered-pair factor two changes the actual factorial.
example : ¬(3 : ℝ)*(1 : ℝ)=6 := by norm_num
example : (Nat.choose 2 2:ℝ)*2*((2-2).factorial:ℝ)=(Nat.factorial 2:ℝ) :=
  endpoint_choose_two_factorial (by decide)

-- One positive column: all three independent-row pairs collide.
private noncomputable def oneColumn : Board 3 1 := fun _ _ => 1/3
private theorem oneColumn_probability : IsProbability oneColumn := by
  constructor
  · intro i j
    norm_num [oneColumn]
  · norm_num [totalMass,rowSum,oneColumn]
example : (∑ j,((colSum oneColumn j)^2-(endpointLeadingColumnCost oneColumn j)^2))=2/9 := by
  rw [endpointLeading_cost_deficit_identity (by decide) oneColumn oneColumn_probability]
  · have h := rowCollisionIntensity_eq (normalizeRows oneColumn)
      (normalizeRows_rowSum oneColumn (fun i => by norm_num [rowSum,oneColumn]))
    norm_num [rowSum,colSum,normalizeRows,oneColumn,Fin.sum_univ_succ] at h
    have he : rowCollisionIntensity (normalizeRows oneColumn)=3 := by linarith
    rw [he]
    norm_num [endpointLeadingScale,rowSum,oneColumn]
  · intro i
    norm_num [rowSum,oneColumn]
example : (Nat.factorial 3:ℝ)*((∏ i,rowSum oneColumn i)-rookSum oneColumn 3)≤
    (Nat.choose 3 2:ℝ)*∑ j,((colSum oneColumn j)^2-(endpointLeadingColumnCost oneColumn j)^2) :=
  endpoint_row_failure_leading_bound (by decide) oneColumn oneColumn_probability

-- A zero row is in the theorem's domain, without normalized-row positivity.
private noncomputable def zeroRowBoard : Board 3 2 := !![0,0;1/2,0;0,1/2]
private theorem zeroRowBoard_probability : IsProbability zeroRowBoard := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [zeroRowBoard]
  · norm_num [totalMass,rowSum,zeroRowBoard,Fin.sum_univ_succ]
example : (∑ j,((colSum zeroRowBoard j)^2-(endpointLeadingColumnCost zeroRowBoard j)^2))=0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [endpointLeadingColumnCost_sq (by decide) zeroRowBoard zeroRowBoard_probability,
    endpointLeadingColumn_zero_row zeroRowBoard zeroRowBoard_probability.1 0
      (by norm_num [rowSum,zeroRowBoard,Fin.sum_univ_succ]) j]
  ring
example : ¬∀ i,0<rowSum zeroRowBoard i := by
  intro h
  have hi := h 0
  norm_num [rowSum,zeroRowBoard,Fin.sum_univ_succ] at hi
example : (1-(Nat.factorial 3:ℝ)*elementarySymmetric (colSum zeroRowBoard) 3)-
    (Nat.choose 3 2:ℝ)*∑ j,((colSum zeroRowBoard j)^2-(endpointLeadingColumnCost zeroRowBoard j)^2)≤
      1-separationProbability zeroRowBoard 3 :=
  endpoint_failure_leading_lower (by decide) zeroRowBoard zeroRowBoard_probability

#print axioms endpointLeadingColumnCost_sq
#print axioms endpointLeading_cost_deficit_identity
#print axioms endpoint_choose_two_factorial
#print axioms endpoint_row_failure_leading_bound
#print axioms endpoint_failure_leading_lower

end DittertRybin.Tests
