import DR.Endpoint.NearEndpointConditional

namespace DittertRybin.Tests
open Certificates

-- Every finite endpoint and the adjacent analytic endpoint retains its floor.
example : nearEndpointRequiredPermanentFloor 21 = (nearEndpointPermanentFloorRat 21 : ℝ) := by
  simp [nearEndpointRequiredPermanentFloor]
example : nearEndpointRequiredPermanentFloor 25 = (nearEndpointPermanentFloorRat 25 : ℝ) := by
  simp [nearEndpointRequiredPermanentFloor]
example : nearEndpointRequiredPermanentFloor 26 = boundaryPermanentFloor 27*(1+1/2500) := by
  norm_num [nearEndpointRequiredPermanentFloor]

-- Closed parameter boundaries, including two zero exceptional diagonals.
example : nearEndpointRequiredPermanentFloor 21 < twoZeroReducedPermanent 20 (1/20) (1/20) :=
  nearEndpointRequiredPermanentFloor_lt_reduced (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example : nearEndpointRequiredPermanentFloor 26 < twoZeroReducedPermanent 25 0 (1/25) :=
  nearEndpointRequiredPermanentFloor_lt_reduced (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- The full-simplex conclusion is conditional on an actual matrix floor.
example (h : TwoIndependentZeroPermanentBound 22 (nearEndpointRequiredPermanentFloor 21)) :
    UniformMaximizer 21 21 20 := nearEndpoint_uniformMaximizer_of_permanent_bound (by decide) h
example (h : TwoIndependentZeroPermanentBound 26 (nearEndpointRequiredPermanentFloor 25)) :
    UniformMaximizer 25 25 24 := nearEndpoint_uniformMaximizer_of_permanent_bound (by decide) h
example (h : TwoIndependentZeroPermanentBound 27 (nearEndpointRequiredPermanentFloor 26)) :
    UniformMaximizer 26 26 25 := nearEndpoint_uniformMaximizer_of_permanent_bound (by decide) h

-- Positive domination, including c=1, transfers an actual zero without division by deficit.
example {n : ℕ} {P B : Board n n} (hB : ∀ i j,0≤B i j)
    (h : ∀ i j,B i j≤P i j) (hz : ∃i j,P i j=0) : ∃i j,B i j=0 := by
  exact nearEndpoint_zero_of_positive_domination (c := 1) (by norm_num) hB
    (by simpa using h) hz

-- c=0 cannot be substituted into zero inheritance: a positive board is dominated.
example : (∀ _i _j : Fin 1,(0:ℝ)*1≤0) ∧ ¬(∃ _i _j : Fin 1,(1:ℝ)=0) := by
  norm_num

-- The floor domain is vacuous in order one because independent rows cannot exist.
example (v : ℝ) : TwoIndependentZeroPermanentBound 1 v := by
  intro D hD hz
  obtain ⟨i₁,i₂,j₁,j₂,hi,_⟩ := hz
  exact (hi (Subsingleton.elim _ _)).elim

#print axioms nearEndpoint_boundary_contender_impossible_tail
#print axioms nearEndpoint_boundary_contender_impossible_finite
#print axioms nearEndpoint_boundary_contender_impossible_of_permanent_bound
#print axioms nearEndpoint_uniformMaximizer_of_permanent_bound
#print axioms nearEndpointRequiredPermanentFloor_lt_reduced
#print axioms nearEndpoint_permanent_bound_of_reduced_form
end DittertRybin.Tests
