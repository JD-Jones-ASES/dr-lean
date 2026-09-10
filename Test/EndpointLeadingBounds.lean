import DR.Endpoint.LeadingBounds
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- AM--GM is local to the selected factors; an unselected coordinate may be signed.
example : (∏ i∈({0,2} : Finset (Fin 3)),(![0,-100,1] : Fin 3 → ℝ) i)≤
    ((∑ i∈({0,2} : Finset (Fin 3)),(![0,-100,1] : Fin 3 → ℝ) i)/2)^2 := by
  have h := endpoint_finset_prod_le_mean_pow ({0,2} : Finset (Fin 3))
    (![0,-100,1] : Fin 3 → ℝ) (by decide) (by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> norm_num [Matrix.cons_val_two])
  exact h

-- The factor (m-2)! and the diagonal correction both have exact nontrivial values.
example : ((3:ℕ).factorial:ℝ) = 6 := by norm_num
example : endpointLeadingDefect 5=8/45 := by
  norm_num [endpointLeadingDefect,dittertConstant,Nat.factorial]
example : endpointLeadingDefect 3=2/3 := by
  norm_num [endpointLeadingDefect,dittertConstant,Nat.factorial]
example :
    ((5-2).factorial:ℝ)*(∏ a∈((Finset.univ.erase (0:Fin 5)).erase 1),
      (![0,0,1/3,1/3,1/3] : Fin 5 → ℝ) a)=2/9 := by
  have he : (Finset.univ.erase (0:Fin 5)).erase 1={2,3,4} := by decide +kernel
  rw [he]
  rw [Finset.prod_insert (by decide : (2:Fin 5)∉({(3:Fin 5),(4:Fin 5)} : Finset (Fin 5))),
    Finset.prod_insert (by decide : (3:Fin 5)∉({(4:Fin 5)} : Finset (Fin 5))),Finset.prod_singleton]
  change (6:ℝ)*((1/3)*((1/3)*(1/3)))=2/9
  norm_num

private noncomputable def boundaryBoard : Board 3 3 := !![0,0,0;1/2,0,0;0,1/2,0]
private theorem boundaryBoard_probability : IsProbability boundaryBoard := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [boundaryBoard]
  · norm_num [totalMass,rowSum,boundaryBoard,Fin.sum_univ_succ]

-- Actual boundary rows, zero cells, and an entirely empty column are retained.
example : 0<endpointLeadingColumnCost boundaryBoard 0 := by
  apply endpointLeadingColumnCost_pos (by decide) boundaryBoard boundaryBoard_probability
  norm_num [colSum,boundaryBoard,Fin.sum_univ_succ,Matrix.cons_val_two]
example : endpointLeadingColumnCost boundaryBoard 2=0 := by
  apply (endpointLeadingColumnCost_eq_zero_iff (by decide) boundaryBoard boundaryBoard_probability 2).mpr
  norm_num [colSum,boundaryBoard,Fin.sum_univ_succ,Matrix.cons_val_two]
example : Real.sqrt (1-endpointLeadingDefect 3)*colSum boundaryBoard 0≤
    endpointLeadingColumnCost boundaryBoard 0 ∧
    endpointLeadingColumnCost boundaryBoard 0≤colSum boundaryBoard 0 :=
  endpointLeadingColumnCost_bounds (by decide) boundaryBoard boundaryBoard_probability 0

-- AM--GM without its selected-factor nonnegativity condition is false.
example : ¬(((-1:ℝ)*(-1)*2)≤(((-1)+(-1)+2)/3)^3) := by norm_num

#print axioms endpoint_finset_prod_le_mean_pow
#print axioms endpointLeading_complement_bounds
#print axioms endpointLeadingKernel_quadratic_bounds
#print axioms endpointLeadingDefect_bounds
#print axioms endpointLeadingColumnCost_bounds
#print axioms endpointLeadingColumnCost_pos
#print axioms endpointLeadingColumnCost_eq_zero_iff

end DittertRybin.Tests
