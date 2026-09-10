import DR.Endpoint.NearSquare
import DR.Endpoint.Double

namespace DittertRybin.Tests

-- The exact recurrence is checked at its first admissible dimension.
example : distinctUniformProbability 4 2 * (2 : ℝ) =
    (3/2 : ℝ)*distinctUniformProbability 2 1 := by
  convert distinctUniformProbability_double_succ (by decide : 1 ≤ 1) using 1 <;> norm_num

example : (12/5 : ℝ) ≤ (6/5 : ℝ)^5 := by
  convert double_recurrence_binomial_lower (by decide : 5 ≤ 5) using 1
  norm_num

-- An actual nontrivial polynomial weight is covered at the largest exponent sum.
example : (81 : ℝ)^5*(161 : ℝ)^3 ≤ (6/5 : ℝ)*((80 : ℝ)^5*(159 : ℝ)^3) := by
  convert endpoint_double_weight_succ_le (m := 80) (p := 5) (q := 3)
    (by decide) (by decide) using 1 <;> norm_num

example : endpointDoubleBoundarySum 3 1000 ≤ endpointDoubleBoundarySum 3 80 :=
  endpointDoubleBoundarySum_le_base (by decide) (by decide) (by decide)
example : endpointDoubleBoundarySum 5 1000 ≤ endpointDoubleBoundarySum 5 117 :=
  endpointDoubleBoundarySum_le_base (by decide) (by decide) (by decide)

-- Threshold predecessors fail the stated scalar criterion; no finite search
-- is being treated as an all-dimensional theorem or as a counterexample to P2.
set_option maxRecDepth 4096 in
example : ¬endpointDoubleBoundarySum 3 79 < (128/289 : ℝ) := by
  norm_num [endpointDoubleBoundarySum, distinctUniformProbability, dittertConstant,
    Nat.descFactorial, Nat.factorial]
set_option maxRecDepth 4096 in
example : ¬endpointDoubleBoundarySum 5 116 < (128/289 : ℝ) := by
  norm_num [endpointDoubleBoundarySum, distinctUniformProbability, dittertConstant,
    Nat.descFactorial, Nat.factorial]

-- Omitting the arithmetic gain cannot establish the 80×160 base.
set_option maxRecDepth 4096 in
example : ¬endpointDoubleBoundarySum 5 80 < (128/289 : ℝ) := by
  norm_num [endpointDoubleBoundarySum, distinctUniformProbability, dittertConstant,
    Nat.descFactorial, Nat.factorial]

example : UniformMaximizer 117 117 117 ∧ UniformMaximizer 117 117 117 :=
  uniform_maximum_short_endpoint (by decide) (by decide) (by decide)
example : UniformMaximizer 117 234 117 ∧ UniformMaximizer 234 117 117 :=
  uniform_maximum_short_endpoint (by decide) (by decide) (by decide)
example : UniformMaximizer 80 160 80 ∧ UniformMaximizer 160 80 80 :=
  uniform_maximum_double_endpoint (by decide)

-- The full sharp inequality exposes only closed-simplex hypotheses.
example {m n : ℕ} (hm : 117 ≤ m) (hmn : m ≤ n) (hn : n ≤ 2*m)
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue m n m ∧
      (separationProbability P m = uniformSeparationValue m n m ↔ P = uniformBoard m n) :=
  (uniform_maximum_short_endpoint hm hmn hn).1 P ⟨hP, hmass⟩

example {m : ℕ} (hm : 80 ≤ m) (P : Board (2*m) m)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue (2*m) m m ∧
      (separationProbability P m = uniformSeparationValue (2*m) m m ↔ P = uniformBoard (2*m) m) :=
  (uniform_maximum_double_endpoint hm).2 P ⟨hP, hmass⟩

-- Every actual zero-entry board is strict, including at the smaller doubled threshold.
example {m : ℕ} (hm : 80 ≤ m) (P : Board m (2*m)) (hP : IsProbability P)
    (i : Fin m) (j : Fin (2*m)) (hz : P i j = 0) :
    separationProbability P m < uniformSeparationValue m (2*m) m := by
  have h := (uniform_maximum_double_endpoint hm).1 P hP
  by_contra hnot
  have heq := h.2.mp (le_antisymm h.1 (le_of_not_gt hnot))
  rw [heq] at hz
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hU : 0 < uniformBoard m (2*m) i j := by unfold uniformBoard; positivity
  exact (ne_of_gt hU) hz

#print axioms distinctUniformProbability_double_succ
#print axioms one_add_pow_quadratic_lower
#print axioms distinctUniformProbability_double_succ_le
#print axioms distinctUniformProbability_mono_columns
#print axioms endpointDoubleBoundarySum_le_base
#print axioms endpoint_near_square_parameter_base
#print axioms endpoint_double_parameter_base
#print axioms endpoint_near_square_parameter_criterion
#print axioms endpoint_double_parameter_criterion
#print axioms uniform_maximum_short_endpoint
#print axioms uniform_maximum_double_endpoint

end DittertRybin.Tests
