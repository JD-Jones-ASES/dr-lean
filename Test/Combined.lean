import DR.Endpoint.Combined
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- A true repeated cell is a failure witness at every sample order>=2.
example (P : Board 2 3) (hP : IsProbability P) :
    cellSquareSum P≤1-separationProbability P 7 := cellSquareSum_le_failure (by decide) P hP
-- At one draw the claimed event implication would be false.
example : ¬cellSquareSum (uniformBoard 2 2)≤1-separationProbability (uniformBoard 2 2) 1 := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [cellSquareSum,uniformBoard,uniformSeparationValue,distinctUniformProbability,Nat.descFactorial]
example (P : Board 5 1) :
    (colSum P 0)^2≤5*cellSquareSum P := colSum_sq_le_cellSquareSum P 0

-- Closed homogeneity includes zero total degree and signed scaling.
example : elementarySymmetric (fun _ : Fin 0 => (0:ℝ)) 0=1 := by
  simp [elementarySymmetric_eq_powerset_sum]
example : elementarySymmetric (fun i : Fin 2 => (-3:ℝ)*(![2,-1] : Fin 2 → ℝ) i) 2=
    (-3:ℝ)^2*elementarySymmetric (![2,-1] : Fin 2 → ℝ) 2 :=
  endpoint_elementarySymmetric_scale _ _ _
example : 8*(5:ℝ)^2*(Nat.factorial 3:ℝ)≤(5:ℝ)^5 :=
  endpoint_factorial_half_coefficient_guard (by decide)
example : ¬8*(3:ℝ)^2*(Nat.factorial 1:ℝ)≤(3:ℝ)^3 := by norm_num
example : dittertConstant 5*endpointColumnLossFactor 5<1 ∧
    endpointColumnLossFactor 5*(endpointLeadingRho 5)^2<1 :=
  smallRow_scalar_parameters (by decide) (by decide)
example : dittertConstant 15*endpointColumnLossFactor 15<1 ∧
    endpointColumnLossFactor 15*(endpointLeadingRho 15)^2<1 :=
  smallRow_scalar_parameters (by decide) (by decide)

-- The coefficient bound is instantiated on a literal positive retained board.
example : (totalMass (uniformBoard 5 250000))^3/(2*(Nat.factorial 3:ℝ))≤
    averagingCoefficient (uniformBoard 5 250000) 3 := by
  have hP := uniformBoard_isProbability (by decide : 0<5) (by decide : 0<250000)
  apply longColumn_five_coefficient_lower (by decide) (by decide) _ hP.1
  · rw [hP.2]; norm_num
  · intro j
    norm_num [colSum,uniformBoard]

-- First row dimension, both sides of each dispatcher boundary, exact cutoff.
example : UniformMaximizer 5 2500000000000 5 ∧ UniformMaximizer 2500000000000 5 5 :=
  uniform_maximum_combined_endpoint_strip (by decide) (by decide)
example : UniformMaximizer 15 22500000000000 15 :=
  (uniform_maximum_combined_endpoint_strip (by decide) (by decide)).1
example : UniformMaximizer 16 25600000000000 16 :=
  (uniform_maximum_combined_endpoint_strip (by decide) (by decide)).1
example : UniformMaximizer 95 902500000000000 95 :=
  (uniform_maximum_combined_endpoint_strip (by decide) (by decide)).1
example : UniformMaximizer 96 921600000000000 96 :=
  (uniform_maximum_combined_endpoint_strip (by decide) (by decide)).1
example (P : Board 5 2500000000000) (hP : IsProbability P) :
    separationProbability P 5≤uniformSeparationValue 5 2500000000000 5 :=
  ((uniform_maximum_combined_endpoint_strip (m:=5) (n:=2500000000000)
    (by decide) (by decide)).1 P hP).1
example (P : Board 5 2500000000000) (hP : IsProbability P) :
    separationProbability P 5=uniformSeparationValue 5 2500000000000 5 ↔
      P=uniformBoard 5 2500000000000 :=
  ((uniform_maximum_combined_endpoint_strip (m:=5) (n:=2500000000000)
    (by decide) (by decide)).1 P hP).2
example : ¬(5:ℕ)≤4 := by decide
example : ¬100000000000*(5:ℕ)^2≤2499999999999 := by decide

#print axioms cellSquareSum_le_failure
#print axioms endpoint_contender_repeatedCell_column_sq
#print axioms smallRow_initial_loss
#print axioms endpoint_smallRow_contender_caps
#print axioms endpoint_factorial_half_coefficient_guard
#print axioms longColumn_five_coefficient_lower
#print axioms longColumn_five_coefficient_ratio
#print axioms longColumn_five_retained_kernel_posDef
#print axioms uniform_maximum_endpoint_of_longColumn_five_caps
#print axioms uniform_maximum_smallRow_endpoint_strip
#print axioms uniform_maximum_combined_endpoint_strip

end DittertRybin.Tests
