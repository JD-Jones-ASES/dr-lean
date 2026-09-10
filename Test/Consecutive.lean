import DR.Endpoint.Consecutive

namespace DittertRybin.Tests

example : UniformMaximizer 19 20 19 ∧ UniformMaximizer 20 19 19 :=
  uniform_maximum_consecutive_endpoint (by decide)
example : UniformMaximizer 29 30 29 ∧ UniformMaximizer 30 29 29 :=
  uniform_maximum_consecutive_endpoint (by decide)
example : UniformMaximizer 30 31 30 ∧ UniformMaximizer 31 30 30 :=
  uniform_maximum_consecutive_endpoint (by decide)
example : UniformMaximizer 1000 1001 1000 ∧ UniformMaximizer 1001 1000 1000 :=
  uniform_maximum_consecutive_endpoint (by decide)

-- The principal declaration exposes only the closed probability simplex.
example {m : ℕ} (hm : 19 ≤ m) (P : Board m (m+1))
    (hnonneg : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue m (m+1) m ∧
      (separationProbability P m = uniformSeparationValue m (m+1) m ↔ P = uniformBoard m (m+1)) :=
  (uniform_maximum_consecutive_endpoint hm).1 P ⟨hnonneg, hmass⟩
example {m : ℕ} (hm : 19 ≤ m) (P : Board (m+1) m)
    (hnonneg : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue (m+1) m m ∧
      (separationProbability P m = uniformSeparationValue (m+1) m m ↔ P = uniformBoard (m+1) m) :=
  (uniform_maximum_consecutive_endpoint hm).2 P ⟨hnonneg, hmass⟩

-- Every actual zero cell is strict, at both finite and infinite dimensions.
example {m : ℕ} (hm : 19 ≤ m) (P : Board m (m+1)) (hP : IsProbability P)
    (i : Fin m) (j : Fin (m+1)) (hz : P i j = 0) :
    separationProbability P m < uniformSeparationValue m (m+1) m := by
  have h := (uniform_maximum_consecutive_endpoint hm).1 P hP
  by_contra hnot
  have heq := h.2.mp (le_antisymm h.1 (le_of_not_gt hnot))
  rw [heq] at hz
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hU : 0 < uniformBoard m (m+1) i j := by unfold uniformBoard; positivity
  exact (ne_of_gt hU) hz

#print axioms consecutive_contender_positive_cut
#print axioms consecutive_active_cut_dilation_sq
#print axioms consecutive_boundary_contender_impossible
#print axioms uniform_maximum_consecutive_endpoint_finite
#print axioms uniform_maximum_consecutive_endpoint

end DittertRybin.Tests
