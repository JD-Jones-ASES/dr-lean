import DR.Endpoint.ElementaryLowerBound
import DR.Endpoint.Normalization
import DR.Endpoint.FactorialScale

namespace DittertRybin.Tests
open scoped BigOperators

-- Signed exact recurrences are distinct from the nonnegative lower bound.
example : (∑ e : Fin 2 ↪ Fin 2, ∏ i,(![-1,2] : Fin 2 → ℝ) (e i)) = -4 := by
  rw [sum_embeddings_eq_factorial_elementary,elementarySymmetric_top]
  norm_num [Fin.prod_univ_succ]

-- Dropping the ordering factorial already fails on a two-label board.
example : elementarySymmetric (![1,2] : Fin 2 → ℝ) 2 = 2 := by
  rw [elementarySymmetric_top]
  norm_num [Fin.prod_univ_succ]
example : ¬((∑ e : Fin 2 ↪ Fin 2, ∏ i,(![1,2] : Fin 2 → ℝ) (e i)) = 2) := by
  rw [sum_embeddings_eq_factorial_elementary,elementarySymmetric_top]
  norm_num [Fin.prod_univ_succ]

-- The total mass need not be one, and zero-weight coordinates remain present.
example : (2:ℝ)^2≤(2:ℝ)*elementarySymmetric (![1,1,1,1,0] : Fin 5 → ℝ) 2 := by
  have h := elementarySymmetric_lower_of_cap (k:=2) (![1,1,1,1,0] : Fin 5 → ℝ)
    (by intro i; fin_cases i <;> norm_num) 4 1 (by norm_num)
    (by norm_num [Fin.sum_univ_succ])
    (by intro i; fin_cases i <;> norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- Sample order zero uses no positive-coordinate or positive-dimension premise
-- in the exact counting identity.
example (x : Fin 0 → ℝ) : elementarySymmetric x 0 = 1 := by
  have h := sum_embeddings_eq_factorial_elementary (k:=0) x
  simpa using h.symm

-- A cap condition cannot be omitted: two distinct draws from one supported
-- label have zero mass, regardless of the positive total mass.
example : ¬((1/2:ℝ)^2≤(2:ℝ)*elementarySymmetric (![1,0] : Fin 2 → ℝ) 2) := by
  rw [elementarySymmetric_top]
  norm_num [Fin.prod_univ_succ]

example : (2:ℝ)^14*dittertConstant 16<1/32 :=
  endpoint_scaled_factorial_lt_one_thirty_two (m:=16) (by decide)
example : ¬((2:ℝ)^12*dittertConstant 14<1/32) := by
  norm_num [dittertConstant,Nat.factorial]

#print axioms distinctSampleSuccEquiv
#print axioms sum_outside_embedding
#print axioms sum_embeddings_successor
#print axioms sum_embeddings_step_lower
#print axioms elementarySymmetric_lower_of_cap
#print axioms endpoint_scaled_factorial_succ
#print axioms endpoint_scaled_factorial_lt_one_thirty_two
end DittertRybin.Tests
