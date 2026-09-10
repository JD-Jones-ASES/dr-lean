import DR.Endpoint.ConsecutiveCutCertificates
import DR.Endpoint.ConsecutiveCutScalars

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

-- The counted positive, non-whole cut sizes are exactly the source's 3,608 cases.
example : (∑ m ∈ Finset.Icc 19 29, ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+2),
    if 0 < consecutiveDemandRat m (m+1) k l ∧ (k ≠ m ∨ l ≠ m+1)
      then 1 else 0 : ℕ) = 3608 := by decide +kernel

-- First finite dimension, a mixed positive cut, and the last axis cut.
example : ConsecutiveCutCertificate 19 1 19 := consecutiveCutCertificate_checked
  (by decide) (by decide) (by decide) (by decide)
example : ConsecutiveCutCertificate 29 29 1 := consecutiveCutCertificate_checked
  (by decide) (by decide) (by decide) (by decide)

-- Empty and whole cuts have no artificial strict certificate requirement.
example : ConsecutiveCutCertificate 19 0 0 := by decide +kernel
example : ConsecutiveCutCertificate 19 19 20 := by decide +kernel

-- The predecessor fails the scalar certificate, not the P2 conjecture.
example : ¬ConsecutiveCutCertificate 18 1 18 := by decide +kernel

-- Doubling the required strict margin fails at the last dimension's axis cut.
example :
    ¬consecutiveRookFloorRat 29 30 29 1-consecutiveAvoidanceRat 29 30-
      (29 : ℚ)^2*consecutiveCutRat 29 30 29 1*(consecutiveRookFloorRat 29 30 29 1)^2/
        (4*(1-consecutiveAvoidanceRat 29 30)) > consecutiveAvoidanceRat 29 30/1000 := by
  decide +kernel

-- A true rectangle floor can exceed the inherited one-zero floor.
example : endpointConsecutiveRectangleFloor 3 4 2 2 = (1/9 : ℝ) := by
  norm_num [endpointConsecutiveRectangleFloor, dittertConstant, Nat.factorial]
example : endpointConsecutiveCutRookFloor 3 4 2 2 = (4/9 : ℝ) := by
  norm_num [endpointConsecutiveCutRookFloor, endpointConsecutiveRectangleFloor,
    boundaryPermanentFloor, distinctUniformProbability, dittertConstant,
    Nat.factorial, Nat.descFactorial]

-- Signed normalization still retains the exact dimensions, including an empty zero axis.
example : endpointConsecutiveRectangleFloor 3 4 3 2 = dittertConstant 4 := by
  norm_num [endpointConsecutiveRectangleFloor, dittertConstant, Nat.factorial]

-- The exact square completion includes a zero deficit and zero dilation.
example : ¬(1-(0 : ℝ))^19*2 ≤ 1-0 := by
  intro h
  exact endpoint_sized_scaling_contradiction (m := 19) (b := 1) (beta := 2)
    (L := 0) (delta := 0) (t := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

example {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (B : Board m n) (hB : IsProbability B)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ)) (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J)
    (hzero : cutMass B Iᶜ Jᶜ = 0) :
    distinctUniformProbability n m*endpointConsecutiveRectangleFloor m n I.card J.card/
      dittertConstant n ≤ endpointRookRatio B :=
  endpointRookRatio_complement_rectangle_lower_bound hm hmn hB hr hc I J hp hzero

#print axioms consecutiveCutCertificate_checked
#print axioms consecutiveCut_row_cap_checked
#print axioms consecutiveRookFloorRat_cast
#print axioms consecutiveCut_real_certificate
#print axioms endpointRookRatio_complement_rectangle_lower_bound
#print axioms endpointRookRatio_sized_boundary_lower_bound
#print axioms endpoint_sized_scaling_contradiction

end DittertRybin.Tests
