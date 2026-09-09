import DR.Endpoint.DeletedRowBalance
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- Unequal deletion masses are allowed, including a zero deletion coordinate.
example : (∑ i : Fin 2,(1-(2:ℝ)*(((![1/2,1/2] : Fin 2 → ℝ) i-
    (![1/64,0] : Fin 2 → ℝ) i)/(1-1/64)))^2)<1/81 := by
  apply endpoint_deleted_row_sq_lt (by decide) _ _ (1/64)
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num
  · norm_num [Fin.sum_univ_succ]

-- The retained normalized row lower bound is obtained from the actual sum
-- of squares, and does not presuppose positive entries.
example : (2/3:ℝ)/2<(![1/2,1/2] : Fin 2 → ℝ) 0 := by
  apply endpoint_row_lower_of_sq (by decide)
  norm_num [Fin.sum_univ_succ]

-- Omitting the small-deletion assumption can destroy retained row balance.
example : ¬((∑ i : Fin 2,(1-(2:ℝ)*(((![1/2,1/2] : Fin 2 → ℝ) i-
    (![1/2,0] : Fin 2 → ℝ) i)/(1-1/2)))^2)<1/81) := by
  norm_num [Fin.sum_univ_succ]

-- With no deletion, a zero original row still violates the required contender
-- concentration; positivity is not granted to arbitrary sparse matrices.
example : ¬((∑ i : Fin 2,((2:ℝ)*(![1,0] : Fin 2 → ℝ) i-1)^2)<1/1024) := by
  norm_num [Fin.sum_univ_succ]

example {m n : ℕ} (hm : 1≤m) {P : Board m n} (hP : IsProbability P)
    (S : Finset (Fin n)) (hw : (m:ℝ)*(1-totalMass (keepColumns P S))≤1/16)
    (hr : (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/1024) :
    (∑ i,(1-(m:ℝ)*(rowSum (keepColumns P S) i/totalMass (keepColumns P S)))^2)<1/81 :=
  endpoint_kept_row_sq_lt hm hP S hw hr

#print axioms endpoint_deleted_row_sq_lt
#print axioms endpoint_kept_row_sq_lt
#print axioms endpoint_row_lower_of_sq
end DittertRybin.Tests
