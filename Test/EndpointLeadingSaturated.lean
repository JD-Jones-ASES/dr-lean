import DR.Endpoint.LeadingSaturated
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The capped product statement retains the closed upper edge.
example : (∏ i, (![2,1/2,1/2] : Fin 3 → ℝ) i)≤
    Real.exp (-(∑ i,((![2,1/2,1/2] : Fin 3 → ℝ) i-1)^2)/8) := by
  apply endpoint_capped_product_exp
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
example : (∏ _i : Fin 0,(1:ℝ))≤Real.exp (-(∑ _i : Fin 0,((1:ℝ)-1)^2)/8) := by
  apply endpoint_capped_product_exp <;> norm_num

-- Dropping the coordinate cap invalidates the scalar logarithm estimate.
example : ¬Real.log (16:ℝ)≤16-1-(16-1)^2/8 := by
  have h := Real.log_nonneg (by norm_num : (1:ℝ)≤16)
  linarith only [h]

example : (0:ℝ)/(8*(1+0))≤1-Real.exp (-0/8) := by
  exact endpoint_one_sub_exp_lower (by norm_num)
example : (1/2000:ℝ)*17/(16*(1+17))≤
    Real.sqrt (1-(1/2000)*Real.exp (-17/8))-Real.sqrt (1-1/2000) :=
  endpoint_sqrt_exp_gap (by norm_num) (by norm_num) (by norm_num)
example : (1:ℝ)*0/(16*(1+0))≤Real.sqrt (1-1*Real.exp (-0/8))-Real.sqrt (1-1) :=
  endpoint_sqrt_exp_gap (by norm_num) (by norm_num) (by norm_num)

-- The saturated denominator cannot be omitted at large variance.
example : ¬(1000:ℝ)/16≤Real.sqrt (1-Real.exp (-1000/8)) := by
  have h : Real.sqrt (1-Real.exp (-1000/8))≤1 := by
    apply Real.sqrt_le_one.mpr
    linarith [Real.exp_pos (-1000/8)]
  linarith only [h]

-- The penalty is smooth even at zero variance on the actual domain.
example : endpointSaturatedPenalty 96 (1/96)=0 := endpointSaturatedPenalty_uniform 96
example : HasDerivAt (endpointSaturatedPenalty 96) (dittertConstant 96*96^2/1000) (1/96) := by
  convert hasDerivAt_endpointSaturatedPenalty (m:=96) (q:=1/96) (by norm_num) using 1
  norm_num

-- Its pole is outside the attainable row-square domain; real division remains totalized.
example : endpointSaturatedPenalty 5 (1/5-1/25)=0 := by
  norm_num [endpointSaturatedPenalty]
example : ¬∃ r : Fin 5 → ℝ, (∑ i,r i)=1 ∧ (∑ i,(r i)^2)=1/5-1/25 := by
  rintro ⟨r,hs,hq⟩
  have h := marginalVariance_nonneg r
  rw [marginalVariance_eq_sum_sq (by decide) hs,hq] at h
  norm_num at h

example : ∃ P : Board 96 1, IsEndpointGaugeMinimum P (endpointSaturatedPenalty 96) :=
  exists_endpointSaturatedMinimum (by decide) (by decide)

-- Actual full-simplex inputs, with no support or stationarity hypothesis.
example (P : Board 96 7) (hP : IsProbability P) :
    (dittertConstant 96/1000)*(96^2*marginalVariance (rowSum P)/(1+96^2*marginalVariance (rowSum P)))≤
      (endpointLeadingGauge P)^2-(1-dittertConstant 96) :=
  endpointLeadingGauge_saturated_sq_gap (by decide) P hP
example (P : Board 96 1) (hP : IsProbability P) :
    1-dittertConstant 96≤(endpointLeadingGauge P)^2 :=
  endpointLeadingGauge_sq_lower (by decide) P hP
example (P : Board 96 2) (hP : IsProbability P) (hz : rowSum P 0=0) :
    endpointLeadingGauge P=1 := endpointLeadingGauge_zero_row P hP 0 hz

#print axioms endpoint_capped_product_exp
#print axioms endpoint_marginal_product_exp
#print axioms endpoint_sqrt_exp_gap
#print axioms endpointLeadingGauge_saturated_norm_gap
#print axioms hasDerivAt_endpointSaturatedPenalty
#print axioms endpointSaturatedPenalty_continuousOn
#print axioms exists_endpointSaturatedMinimum
#print axioms IsEndpointGaugeMinimum.saturated_kernel
#print axioms endpointLeadingGauge_saturated_lower
#print axioms endpointLeadingGauge_saturated_sq_gap

end DittertRybin.Tests
