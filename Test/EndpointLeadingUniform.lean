import DR.Endpoint.LeadingConstants
import DR.Endpoint.LeadingNorm
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

example : endpointLeadingDefect 5=(8/45:ℝ) := by
  norm_num [endpointLeadingDefect,dittertConstant,Nat.factorial]
example : dittertConstant 10<1/1000 := endpointLeading_alpha_lt_thousandth (by decide)
example : endpointLeadingRatioCap 96-1<(1332/275:ℝ)*dittertConstant 96 :=
  endpointLeadingRatioCap_sub_one_lt (by decide)
example : ¬dittertConstant 5<1/1000 := by norm_num [dittertConstant,Nat.factorial]
example : dittertConstant 1*(1-1/(1+2:ℝ))=
    dittertConstant 3*(1+2/(1:ℝ))^1 := by
  simpa only [Nat.cast_one] using endpointLeading_defect_ratio_identity (by decide : 0<1)

-- Uniform cost has the actual column factor; the whole gauge does not.
example (j : Fin 7) : endpointLeadingColumnCost (uniformBoard 5 7) j=
    (1/7)*Real.sqrt (1-dittertConstant 5) :=
  endpointLeadingColumnCost_uniform (by decide) (by decide) j
example : endpointLeadingGauge (uniformBoard 5 7)=Real.sqrt (1-dittertConstant 5) :=
  endpointLeadingGauge_uniform (by decide) (by decide)
example : endpointLeadingGauge (uniformBoard 5 0)=0 := by
  simp [endpointLeadingGauge]
example : ¬endpointLeadingGauge (uniformBoard 5 0)=Real.sqrt (1-dittertConstant 5) := by
  simp only [endpointLeadingGauge,Finset.univ_eq_empty,Finset.sum_empty]
  have hpos : 0<Real.sqrt (1-dittertConstant 5) := by
    apply Real.sqrt_pos.mpr
    norm_num [dittertConstant,Nat.factorial]
  exact ne_of_lt hpos

-- The exact marginal identity retains signed and zero coordinates.
example : quadraticValue (endpointLeadingKernel (![2,-1,0] : Fin 3 → ℝ)) ![2,-1,0]=1 := by
  rw [endpointLeadingKernel_marginal_value (by decide)]
  norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ]
example : endpointLeadingScale (![0,1/3,2/3] : Fin 3 → ℝ)≤
    dittertConstant 3/(3*(3-1)) := by
  apply endpointLeadingScale_le (by decide)
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]

-- The norm theorem covers a singular zero form and an empty vector family.
example (v : Fin 3 → Fin 2 → ℝ) :
    Real.sqrt (quadraticValue (0 : Matrix (Fin 2) (Fin 2) ℝ) (fun i => ∑ a,v a i))≤
      ∑ a,Real.sqrt (quadraticValue (0 : Matrix (Fin 2) (Fin 2) ℝ) (v a)) := by
  apply endpoint_quadratic_sqrt_sum_le
  exact Matrix.PosSemidef.zero
example (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosSemidef) :
    Real.sqrt (quadraticValue Q (fun i => ∑ a : Fin 0, (fun _ : Fin 0 => (fun _ : Fin 2 => (3:ℝ))) a i))≤0 := by
  simpa only [Finset.univ_eq_empty,Finset.sum_empty] using
    endpoint_quadratic_sqrt_sum_le Q hQ (fun _ : Fin 0 => fun _ : Fin 2 => (3:ℝ))

-- A signed vector does not turn a negative quadratic into a norm.
example : (quadraticValue (!![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℝ) ![0,1])<0 := by
  norm_num [quadraticValue,Fin.sum_univ_succ]

#print axioms endpointLeadingDefect_lt_alpha_ratio
#print axioms endpointLeadingRatioCap_sub_one_lt
#print axioms endpointLeadingKernel_marginal_value
#print axioms endpointLeadingGauge_uniform
#print axioms endpointLeadingScale_le
#print axioms endpointBilinear_le_sqrt
#print axioms endpoint_quadratic_sqrt_sum_le
#print axioms endpointLeadingGauge_product_lower

end DittertRybin.Tests
