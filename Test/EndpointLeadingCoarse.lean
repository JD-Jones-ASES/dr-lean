import DR.Endpoint.LeadingCoarse
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The scalar certificate holds at the first row dimension and for arbitrary signed d.
example : (0:ℝ)<(601/625)*(1+3*2)*(11+3*2)-4*(2*2-1)*(11-2*2) := by
  convert endpoint_coarse_interval_discriminant (k:=3) (by norm_num) 2 using 1
  norm_num
example : (0:ℝ)<(601/625)*(1+3*(-7/3))*(11+3*(-7/3))-
    4*(2*(-7/3)-1)*(11-2*(-7/3)) := by
  convert endpoint_coarse_interval_discriminant (k:=3) (by norm_num) (-7/3) using 1
  norm_num
-- The k>=3 guard cannot simply be omitted from this scalar certificate.
example : ¬(0:ℝ)<(601/625)*(1+1*2)*(11+1*2)-2*(2*2-1)*(11-2*2) := by norm_num
example : (2:ℝ)/(11+3*2)+2/(1+3*2)-5*(2/(11+3*2))*(2/(1+3*2))<
    1/5+(601/625)/(5*4) := by
  convert endpoint_coarse_interval_bound (k:=3) (d:=2) (T:=11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

-- Closed-simplex product stability includes a zero coordinate.
example : (∏ i : Fin 2,(2:ℝ)*(![1,0] : Fin 2 → ℝ) i)≤
    1-marginalVariance (![1,0] : Fin 2 → ℝ) := by
  apply endpoint_product_le_one_sub_variance (by decide)
  · intro i; fin_cases i <;> norm_num
  · norm_num
example : (∏ i : Fin 3,(3:ℝ)*(![3,-1,-1] : Fin 3 → ℝ) i)>
    1-marginalVariance (![3,-1,-1] : Fin 3 → ℝ) := by
  norm_num [marginalVariance,Fin.sum_univ_succ,Fin.prod_univ_succ]
example : endpointCoarsePenalty 5 (1/5)=0 := endpointCoarsePenalty_uniform 5
example : HasDerivAt (endpointCoarsePenalty 5) (dittertConstant 5/1000) 0 :=
  hasDerivAt_endpointCoarsePenalty 5 0

-- The gauge theorem is genuinely valid with fewer columns than rows.
example : endpointLeadingGauge (uniformBoard 5 1)=Real.sqrt (1-dittertConstant 5) :=
  endpointLeadingGauge_uniform (by decide) (by decide)
example (P : Board 5 1) (hP : IsProbability P) :
    Real.sqrt (1-dittertConstant 5)+(dittertConstant 5/1000)*marginalVariance (rowSum P)≤
      endpointLeadingGauge P := endpointLeadingGauge_coarse_lower (by decide) P hP
example (P : Board 5 2) (hP : IsProbability P) :
    (1-dittertConstant 5+(dittertConstant 5/1000)*marginalVariance (rowSum P))/2≤
      ∑ j,quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j) :=
  endpointLeading_quadratic_coarse_lower (by decide) (by decide) P hP

private noncomputable def boundaryBoard : Board 5 1 := fun i _ => if i=0 then 1 else 0
private theorem boundaryBoard_probability : IsProbability boundaryBoard := by
  constructor
  · intro i j; unfold boundaryBoard; split_ifs <;> norm_num
  · norm_num [totalMass,rowSum,boundaryBoard,Fin.sum_univ_succ]
example : endpointLeadingGauge boundaryBoard=1 := by
  apply endpointLeadingGauge_zero_row boundaryBoard boundaryBoard_probability (1 : Fin 5)
  norm_num [rowSum,boundaryBoard]
example : (dittertConstant 5/1000)*marginalVariance (rowSum boundaryBoard)≤
    (endpointLeadingGauge boundaryBoard)^2-(1-dittertConstant 5) :=
  endpointLeadingGauge_coarse_sq_gap (by decide) boundaryBoard boundaryBoard_probability

#print axioms endpoint_coarse_interval_discriminant
#print axioms endpoint_coarse_rows_square_bound
#print axioms endpoint_coarse_stationary_kernel
#print axioms endpoint_product_le_one_sub_variance
#print axioms endpointLeadingGauge_coarse_norm_gap
#print axioms exists_endpointCoarseMinimum
#print axioms IsEndpointGaugeMinimum.coarse_kernel
#print axioms endpointLeadingGauge_coarse_lower
#print axioms endpointLeadingGauge_coarse_sq_gap
#print axioms endpointLeading_quadratic_coarse_lower

end DittertRybin.Tests
