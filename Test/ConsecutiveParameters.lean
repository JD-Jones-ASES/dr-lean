import DR.Endpoint.ConsecutiveLarge

namespace DittertRybin.Tests

-- Adjacent-column normalization retains the extra factor m+1, even at m=0.
example : distinctUniformProbability 1 0 = dittertConstant 1 := by
  simpa using distinctUniformProbability_consecutive 0
example : distinctUniformProbability 4 3 = (4 : ℝ)*dittertConstant 4 := by
  convert distinctUniformProbability_consecutive 3 using 1
  norm_num

example : endpointConsecutiveBoundarySum 31 ≤ endpointConsecutiveBoundarySum 30 :=
  endpointConsecutiveBoundarySum_succ_le (by decide)
example : endpointConsecutiveBoundarySum 1000 < (512/289 : ℝ) :=
  endpointConsecutiveBoundarySum_lt (by decide)

-- The coarse scalar criterion does not cover the immediately preceding dimension.
example : ¬endpointConsecutiveBoundarySum 29 < (512/289 : ℝ) := by
  norm_num [endpointConsecutiveBoundarySum, dittertConstant, Nat.factorial]

example : UniformMaximizer 30 31 30 ∧ UniformMaximizer 31 30 30 :=
  uniform_maximum_consecutive_endpoint_of_thirty_le (by decide)
example {m : ℕ} (hm : 30 ≤ m) (P : Board m (m+1))
    (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue m (m+1) m ∧
      (separationProbability P m = uniformSeparationValue m (m+1) m ↔ P = uniformBoard m (m+1)) :=
  (uniform_maximum_consecutive_endpoint_of_thirty_le hm).1 P ⟨hP, hmass⟩

#print axioms distinctUniformProbability_consecutive
#print axioms endpoint_consecutive_weight_succ_le
#print axioms endpointConsecutiveBoundarySum_succ_le
#print axioms endpoint_consecutive_parameter_base
#print axioms endpointConsecutiveBoundarySum_lt
#print axioms endpoint_consecutive_parameter_criterion
#print axioms uniform_maximum_consecutive_endpoint_of_thirty_le

end DittertRybin.Tests
