import DR.Endpoint.TransitionDeletion
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- This original row budget lies below 1/100 but above the earlier LLL
-- strip's 1/1024 threshold; the transition estimate is actually used.
example : (∑ i : Fin 2,((2:ℝ)*(![13/25,12/25] : Fin 2 → ℝ) i-1)^2)<1/100 := by
  norm_num [Fin.sum_univ_succ]
example : ¬((∑ i : Fin 2,((2:ℝ)*(![13/25,12/25] : Fin 2 → ℝ) i-1)^2)<1/1024) := by
  norm_num [Fin.sum_univ_succ]
example : (∑ i : Fin 2,(1-(2:ℝ)*(((![13/25,12/25] : Fin 2 → ℝ) i-
    (![1/64,0] : Fin 2 → ℝ) i)/(1-1/64)))^2)<1/9 := by
  apply transition_deleted_row_sq_lt (by decide) _ _ (1/64)
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num
  · norm_num [Fin.sum_univ_succ]

-- Removing the small-deletion hypothesis can lose a complete retained row.
example : ¬((∑ i : Fin 2,(1-(2:ℝ)*(((![1/2,1/2] : Fin 2 → ℝ) i-
    (![1/2,0] : Fin 2 → ℝ) i)/(1-1/2)))^2)<1/9) := by
  norm_num [Fin.sum_univ_succ]

example : 4096*(10^18)^3≤(10^36:ℕ)^2 :=
  endpoint_transition_lower_square (by norm_num) (by norm_num)

-- The exact lower transition boundary is already above the squared LLL
-- lower edge; no rounding convention creates an unproved integer gap.
example : 4096*(10^18)^3≤(((10^18)*(10^18-1)/20:ℕ))^2 :=
  endpoint_transition_lower_square (by norm_num) (by norm_num)

#print axioms deleted_row_sq_scaled_le
#print axioms transition_deleted_row_sq_lt
#print axioms transition_kept_row_sq_lt
#print axioms endpoint_transition_lower_square
#print axioms endpoint_transition_contender_column_cap
#print axioms endpoint_transition_deleted_bounds
end DittertRybin.Tests
