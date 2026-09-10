import DR.Endpoint.TransitionAvoidance

namespace DittertRybin.Tests

-- The complete reciprocal error is retained at its largest allowed scalar
-- values; this is exact rational arithmetic, not an asymptotic expansion.
example : ((20:ℝ)+1/(2*160000000^2))*(1+160000000/160000000)≤
    20+3200000001/160000000 := by
  exact transition_intensity_error_le 160000000 20 160000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (1:ℝ)/(1-5*(6200000/10^18))≤1+6000000000/10^18 := by
  apply transition_log_denominator_bound (10^18) 1 1 <;> norm_num

-- Dropping the positive reciprocal-row correction or the LLL denominator
-- produces false scalar bounds even at the actual dimension threshold.
example : ¬(((1:ℝ)+1/(2*(10^18)^2))*(1+160000000/10^18)≤1) := by norm_num
example : ¬((1:ℝ)/(1-5*(6200000/10^18))≤1) := by norm_num

-- A genuine nonempty transition dimension pair. All probability inputs are
-- the actual original row law of this probability board.
example (P : Board (10^18) (10^36)) (hP : IsProbability P)
    (hcont : uniformSeparationValue (10^18) (10^36) (10^18)≤separationProbability P (10^18)) :
    distinctUniformProbability (10^36) (10^18)*Real.exp (-7000000000/((10^18:ℕ):ℝ))≤
      originalRowAvoidance P := by
  apply endpoint_transition_original_avoidance_relative (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hP hcont

example {m n : ℕ} (hm : 10^18≤m) (hmn : m≤n)
    (hl : m*(m-1)≤20*n) (hu : n≤10000*m^2)
    (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    0<originalRowAvoidance P ∧
      -Real.log (originalRowAvoidance P)≤(m:ℝ)^2/(2*(n:ℝ))+6000000000/(m:ℝ) :=
  endpoint_transition_original_log_bound hm hmn hl hu hP hcont

#print axioms transition_intensity_error_le
#print axioms transition_log_denominator_bound
#print axioms endpoint_transition_collision_bounds
#print axioms endpoint_transition_original_log_bound
#print axioms endpoint_transition_original_avoidance_relative
end DittertRybin.Tests
