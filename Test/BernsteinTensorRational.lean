import DR.Certificates.BernsteinTensorRational
import Mathlib.Algebra.Algebra.Rat

namespace DittertRybin.Tests.BernsteinTensorRational
open DittertRybin.Certificates

-- Conversion retains arbitrary signed rational data and a remaining polynomial axis.
example : algebraBernsteinCoefficient
    (fun k : Fin 3 => algebraMap ℚ ℝ (![1,-2,3] k)) 1 = 0 := by
  rw [algebraBernsteinCoefficient_map_rat]
  norm_num [powerToBernstein, Fin.sum_univ_succ]

-- The mixed coefficient at degrees (1,1) is half in each converted axis.
example : powerToBernstein
    (fun b : Fin 3 => powerToBernstein
      (fun a : Fin 3 => if a = 1 ∧ b = 1 then (1 : ℚ) else 0) 1) 1 = 1/4 := by
  norm_num [powerToBernstein, Fin.sum_univ_succ]

#print axioms DittertRybin.Certificates.algebraBernsteinCoefficient_map_rat
#print axioms DittertRybin.Certificates.double_bernstein_coefficient_power_sum
end DittertRybin.Tests.BernsteinTensorRational
