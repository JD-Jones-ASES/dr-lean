import DR.Endpoint.NearEndpointParameters

namespace DittertRybin.Tests

example : nearEndpointScaleWeight 26 < (3/4 : ℝ) := nearEndpointScaleWeight_base

-- The chosen sufficient scalar threshold is a real boundary of this estimate.
set_option maxRecDepth 4096 in
example : 1 < nearEndpointScaleWeight 25 := by
  norm_num [nearEndpointScaleWeight,dittertConstant,Nat.factorial]

example {n : ℕ} (hn : 26 ≤ n) :
    distinctUniformProbability n (n-1) < 3/(5*((n : ℝ)-1)^4*(n : ℝ)^2) :=
  nearEndpoint_uniform_small hn

example : distinctUniformProbability 100 99 < 1/4 :=
  (nearEndpoint_parameter_bounds (by decide : 26 ≤ 100)).1

example : 1/(5*(2 : ℝ)^2) < ((1+1/(4*(2 : ℝ)^2))-1)/(1+1/(4*(2 : ℝ)^2))^2 :=
  nearEndpoint_gap_scalar (by norm_num)

-- Dropping the m≥2 guard makes the scalar gap assertion false.
example : ¬(1/(5*(1 : ℝ)^2) < ((1+1/(4*(1 : ℝ)^2))-1)/(1+1/(4*(1 : ℝ)^2))^2) := by
  norm_num

#print axioms nearEndpoint_polynomial_weight_step
#print axioms nearEndpointScaleWeight_step
#print axioms nearEndpointScaleWeight_lt_one
#print axioms nearEndpoint_uniform_small
#print axioms nearEndpoint_gap_scalar
#print axioms nearEndpoint_parameter_bounds
end DittertRybin.Tests
