import DR.Endpoint.TransitionBootstrap

namespace DittertRybin.Tests
open scoped BigOperators

-- The zero-error boundary is valid and retains the actual avoidance ratio.
example : ((1/2:ℝ)-1/2)/(1-1/2)≤40001*0 :=
  transition_avoidance_ratio_deficit_le (1/2) (1/2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- An omitted avoidance comparison would make the zero-error claim false.
example : ¬(((1/2:ℝ)-0)/(1-0)≤40001*0) := by norm_num

-- The retained collision-free denominator cannot be replaced by one.
example : ¬(((1/2:ℝ)-1/4)/(1-1/4)≤(1/2-1/4)) := by norm_num

-- Exact threshold arithmetic is sufficient for the bootstrap constants.
example : (40001:ℝ)*(7000000000/10^18)<1/2000 := by norm_num
example : (8:ℝ)/1999<1/100 := by norm_num

-- Full closed-simplex row concentration at a nonempty transition instance;
-- no stationary condition, positive-entry premise or row shape is supplied.
example (P : Board (10^18) (10^36)) (hP : IsProbability P)
    (hcont : uniformSeparationValue (10^18) (10^36) (10^18)≤separationProbability P (10^18)) :
    (∑ i,(((10^18:ℕ):ℝ)*rowSum P i-1)^2)<1/100 := by
  exact endpoint_transition_scaled_row_sq_lt (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hP hcont

example {m n : ℕ} (hm : 10^18≤m) (hmn : m≤n)
    (hl : m*(m-1)≤20*n) (hu : n≤10000*m^2)
    (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    1-endpointRowProduct P<1/2000 :=
  endpoint_transition_rowProduct_deficit_lt hm hmn hl hu hP hcont

#print axioms transition_avoidance_ratio_deficit_le
#print axioms endpoint_transition_rowProduct_deficit_lt
#print axioms endpoint_transition_scaled_row_sq_lt
end DittertRybin.Tests
