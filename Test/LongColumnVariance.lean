import DR.Endpoint.LongColumnAbsorption
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

example : centeredVariance (![11/16,1/4] : Fin 2 → ℝ)=49/512 := by
  norm_num [centeredVariance,Fin.sum_univ_succ]

-- The costs need not have total mass one; centering at uniform is different.
example : (∑ j, (![11/16,1/4] : Fin 2 → ℝ) j)=15/16 := by norm_num
example : centeredVariance (![11/16,1/4] : Fin 2 → ℝ)≠
    marginalVariance (![11/16,1/4] : Fin 2 → ℝ) := by
  norm_num [centeredVariance,marginalVariance,Fin.sum_univ_succ]

example : marginalVariance (![3/4,1/4] : Fin 2 → ℝ)≤
    3*centeredVariance (![11/16,1/4] : Fin 2 → ℝ)+3*(1/10:ℝ)^2/2 := by
  apply longColumn_variance_conversion (by decide)
    (![3/4,1/4] : Fin 2 → ℝ) (![11/16,1/4] : Fin 2 → ℝ)
  · intro j; fin_cases j <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> norm_num

example : marginalVariance (![1,0] : Fin 2 → ℝ)≤
    3*centeredVariance (![15/16,0] : Fin 2 → ℝ)+3*(1/16:ℝ)^2/2 := by
  apply longColumn_variance_conversion (by decide)
    (![1,0] : Fin 2 → ℝ) (![15/16,0] : Fin 2 → ℝ)
  · intro j; fin_cases j <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> norm_num

example : centeredVariance (fun i : Fin 0 => (Fin.elim0 i : ℝ))=0 := by
  simp [centeredVariance]

-- Two tempting changes to the variance/coordinate bounds are invalid.
example : ¬(2:ℝ)/(1-2/64)≤2 := by norm_num
example : ¬(1:ℝ)^2≤4/3^2+4*centeredVariance (fun _ : Fin 3 => (0:ℝ)) := by
  norm_num [centeredVariance]

example (P : Board 5 2) (hP : IsProbability P) :
    marginalVariance (colSum P)≤3*centeredVariance (endpointLeadingColumnCost P)+
      3*(endpointLeadingRho 5)^2/2 :=
  endpointLeading_variance_conversion (by decide) (by decide) P hP

example : (0:ℝ)+(100/2)*(1/100000000)≤
    (1/1000)*2/(2*100)+3*2*(1/10000)^2*(1/100) := by norm_num

example : (1/100:ℝ)<25/100 := by
  apply longColumn_cap_twenty_five (a:=1/1000) (b:=2) (ρ:=1/10000)
    (W:=1/100000000) (g:=0) <;> norm_num

-- The terminal quadratic has a strict positive margin at the proposed cap.
example : (25:ℝ)^2-24*25-8=17 := by norm_num

#print axioms longColumn_variance_conversion
#print axioms longColumn_coordinate_sq_le
#print axioms endpointLeadingRho_bounds
#print axioms endpointLeading_variance_conversion
#print axioms endpointLeading_column_sq_le
#print axioms longColumn_absorb_variance
#print axioms longColumn_cap_twenty_five
#print axioms longColumn_gap_after_cap

end DittertRybin.Tests
