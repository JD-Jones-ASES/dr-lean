import DR.Endpoint.EndpointCoefficient
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The actual all-dimension coefficient guard, including its exact base.
example : 4*(16:ℝ)^2*2^14*((14:ℕ).factorial:ℝ)≤(16:ℝ)^16 :=
  endpoint_factorial_coefficient_guard (by decide : 16≤16)
example {m : ℕ} (hm : 16≤m) :
    4*(m:ℝ)^2*(2:ℝ)^(m-2)*((m-2).factorial:ℝ)≤(m:ℝ)^m :=
  endpoint_factorial_coefficient_guard hm

-- Nonunit mass and zero cells are retained in the actual row-product scale.
private noncomputable def P : Board 2 2 := ![![2,0],![0,3]]
example : (∏ i,rowSum P i)/(totalMass P)^2≤(totalMass P)^0/(2:ℝ)^2 := by
  apply endpoint_row_product_scale_le (by decide) P
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [P]
  · norm_num [P,totalMass,rowSum,Fin.sum_univ_succ]

-- Removing the mass-square factor from the left is false on that board.
example : ¬((∏ i,rowSum P i)≤(totalMass P)^0/(2:ℝ)^2) := by
  norm_num [P,rowSum,Fin.sum_univ_succ,Fin.prod_univ_succ]

-- The probability denominator is the actual normalized retained row law;
-- positivity is retained as an explicit hypothesis of this generic lemma.
example {m n : ℕ} (hm : 16≤m) (Q : Board m n) (hQ : ∀ i j,0≤Q i j)
    (hr : ∀ i,0<rowSum Q i) (hh : 0<totalMass Q)
    (hp : 0<rowAvoidance (normalizeRows Q)) (c : ℝ)
    (hc : ∀ j,colSum Q j≤c) (hk : ((m-2:ℕ):ℝ)*c≤totalMass Q/2) :
    4*(m:ℝ)^2≤averagingCoefficient Q (m-2)/
      (((∏ i,rowSum Q i)/(totalMass Q)^2)*rowAvoidance (normalizeRows Q)) :=
  endpoint_coefficient_ratio_lower hm Q hQ hr hh hp c hc hk

#print axioms endpoint_factorial_coefficient_guard
#print axioms endpoint_row_product_scale_le
#print axioms endpoint_coefficient_ratio_lower
end DittertRybin.Tests
