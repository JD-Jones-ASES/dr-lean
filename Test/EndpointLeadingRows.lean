import DR.Endpoint.LeadingRows
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

private noncomputable def rowLaw : Board 3 3 := !![1,0,0;0,1,0;1/2,1/2,0]
private theorem rowLaw_normalized (i : Fin 3) : rowSum rowLaw i=1 := by
  fin_cases i <;> norm_num [rowSum,rowLaw,Fin.sum_univ_succ]
private noncomputable def masses : Fin 3 → ℝ := ![1/2,1/3,1/6]
private noncomputable def direction : Fin 3 → ℝ := ![1,-1,0]
private theorem masses_nonzero (i : Fin 3) : masses i≠0 := by
  fin_cases i <;> norm_num [masses]

-- Literal nonidentical-row collision and cost, with the full (m-2)! factor.
example : endpointLeadingColumnCollision rowLaw 0=1 := by
  norm_num [endpointLeadingColumnCollision,rowLaw,Fin.sum_univ_succ]
example : endpointLeadingScale masses=1/36 := by
  norm_num [endpointLeadingScale,masses,Fin.prod_univ_succ,Nat.factorial]
example : quadraticValue (endpointLeadingKernel (rowSum (endpointRowBoard masses rowLaw)))
    (fun i => endpointRowBoard masses rowLaw i 0)=5/16 := by
  rw [endpointLeadingColumn_polynomial masses rowLaw rowLaw_normalized]
  norm_num [endpointLeadingScale,endpointLeadingColumnCollision,masses,rowLaw,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Nat.factorial]

-- This derivative is nonzero: no stationarity is inferred from a probability board.
example : HasDerivAt (fun t : ℝ =>
    quadraticValue (endpointLeadingKernel (rowSum
      (endpointRowBoard (fun i => masses i+t*direction i) rowLaw)))
      (fun i => endpointRowBoard (fun i => masses i+t*direction i) rowLaw i 0)) (43/36) 0 := by
  have h := hasDerivAt_endpointLeadingColumn_polynomial masses direction rowLaw
    rowLaw_normalized masses_nonzero 0
  norm_num [masses,direction,rowLaw,endpointLeadingScale,endpointLeadingColumnCollision,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Nat.factorial] at h
  exact h

-- The entirely empty third column is identically zero under every real row scaling.
example (r : Fin 3 → ℝ) : endpointLeadingColumnCost (endpointRowBoard r rowLaw) 2=0 := by
  apply endpointLeadingColumnCost_zero_column
  intro i
  fin_cases i <;> norm_num [rowLaw,Matrix.cons_val_two]

-- Both zero and negative row masses are allowed in the underlying polynomial identity.
example (X : Board 3 4) (hs : ∀ i,rowSum X i=1) (j : Fin 4) :
    quadraticValue (endpointLeadingKernel (rowSum (endpointRowBoard ![0,-2,3] X)))
      (fun i => endpointRowBoard ![0,-2,3] X i j)=
      (∑ i,(![0,-2,3] : Fin 3 → ℝ) i*X i j)^2-
      endpointLeadingScale (![0,-2,3] : Fin 3 → ℝ)*endpointLeadingColumnCollision X j :=
  endpointLeadingColumn_polynomial _ X hs j
example (r : Fin 0 → ℝ) (X : Board 0 0) :
    totalMass (endpointRowBoard r X)=0 := by simp [totalMass]

#print axioms rowSum_endpointRowBoard
#print axioms endpointLeadingColumn_polynomial
#print axioms hasDerivAt_endpointLeadingScale_line
#print axioms hasDerivAt_endpointLeadingColumn_polynomial
#print axioms hasDerivAt_endpointLeadingColumnCost
#print axioms endpointLeadingColumnCost_zero_column

end DittertRybin.Tests
