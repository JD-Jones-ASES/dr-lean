import DR.Endpoint.FactorialDecay

namespace DittertRybin.Tests

-- The recurrence is non-strict at its first allowed step.
example : distinctUniformProbability 2 2 = distinctUniformProbability 1 1 / 2 := by
  norm_num [distinctUniformProbability, Nat.descFactorial_succ]

-- The empty endpoint is normalized to one, and does not obey the half-step bound.
example : distinctUniformProbability 0 0 = 1 ∧
    distinctUniformProbability 0 0 / 2 < distinctUniformProbability 1 1 := by
  norm_num [distinctUniformProbability]

-- The polynomial estimate requires a large-m threshold; it fails already at m=2.
example : 1/(2:ℝ)^14 < distinctUniformProbability 2 2 := by
  norm_num [distinctUniformProbability, Nat.descFactorial_succ]

-- These exact integer controls support the all-m induction, not a finite census.
example : (128:ℝ)^14 < 2^127 := by norm_num
example : (129/128:ℝ)^14 < 2 := by norm_num

example {m : ℕ} (hm : 128 ≤ m) :
    (m.factorial:ℝ)/(m:ℝ)^m ≤ 1/(m:ℝ)^14 := by
  simpa only [distinctUniformProbability,Nat.descFactorial_self] using
    distinctUniformProbability_endpoint_le_inv_fourteenth hm

#print axioms distinctUniformProbability_endpoint_succ_le_half
#print axioms distinctUniformProbability_endpoint_le_half_pow
#print axioms half_pow_mul_fourteenth_le_one
#print axioms distinctUniformProbability_endpoint_le_inv_fourteenth
end DittertRybin.Tests
