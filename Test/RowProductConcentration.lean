import DR.Endpoint.RowProductConcentration
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The logarithm estimate includes the closed upper endpoint y=2.
example : Real.log 2≤7/8 := by
  have h := log_le_sub_one_sub_sq_eighth 2 (by norm_num) le_rfl
  norm_num at h
  exact h

-- Removing either the positive lower domain or the upper cap is invalid.
example : ¬(Real.log 0≤(0:ℝ)-1-((0:ℝ)-1)^2/8) := by norm_num
example : ¬(Real.log 10≤(10:ℝ)-1-((10:ℝ)-1)^2/8) := by
  have h := Real.log_pos (by norm_num : (1:ℝ)<10)
  norm_num
  linarith

-- An exact nonconstant row vector is admitted, with a literal product
-- deficit rather than a stationary or coordinatewise-closeness premise.
example : (∑ i : Fin 2, ((![1+1/256,1-1/256] : Fin 2 → ℝ) i-1)^2)<1/1024 := by
  apply product_deficit_sq_deviation_small (![1+1/256,1-1/256] : Fin 2 → ℝ)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ]) (1/65536) (by norm_num)
  norm_num [Fin.prod_univ_two]

-- The empty host has its true empty product one.
example : (∑ i : Fin 0, ((fun _ : Fin 0 => (0:ℝ)) i-1)^2)<1/1024 := by
  apply product_deficit_sq_deviation_small (fun _ : Fin 0 => (0:ℝ))
    (fun i => Fin.elim0 i) (by simp) 0 (by norm_num)
  simp

-- At product zero, the positivity conclusion is genuinely unavailable.
example : ¬(∀ i : Fin 2,0<(![2,0] : Fin 2 → ℝ) i) := by
  intro h
  have hh := h 1
  norm_num at hh

example {m n : ℕ} (hm : 2≤m) (hmn : m≤n) {P : Board m n}
    (hP : IsProbability P) (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (hb : distinctUniformProbability n m≤1/16384) :
    (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/1024 :=
  endpoint_contender_scaled_row_sq_small hm hmn hP hcont hb

#print axioms log_le_sub_one_sub_sq_eighth
#print axioms coordinate_exp_envelope_le_two_div_exp
#print axioms product_large_coordinate_bounds
#print axioms product_large_sq_deviation_le_log
#print axioms product_deficit_sq_deviation
#print axioms product_deficit_sq_deviation_small
#print axioms endpoint_contender_scaled_row_sq_small

end DittertRybin.Tests
