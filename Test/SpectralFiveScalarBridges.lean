import DR.Certificates.BernsteinPositiveBlend
import DR.Certificates.SpectralFiveSingletonDataPositive
import DR.Certificates.SpectralFiveSingletonBounds
import DR.Certificates.SpectralFiveSingletonMonotonicity
import DR.Certificates.SpectralFiveCrossingMonotonicity

/-! Persistent boundary and denominator controls for the order-five scalar bridges. -/

open DittertRybin.Certificates
open DittertRybin.Certificates.SpectralFiveSingleton
open DittertRybin.Certificates.SpectralFiveTwoBlocks
open scoped BigOperators

-- Every corner retains a positive Bernstein weight, including degree zero.
example : ∃ i : Fin 1, 0 < bernsteinWeight 0 i (0:ℝ) := exists_bernsteinWeight_pos 0 0
example : ∃ i : Fin 8, 0 < bernsteinWeight 7 i (1:ℝ) := exists_bernsteinWeight_pos 7 1
example : 0 < ∑ i : Fin 2, ∑ j : Fin 3,
    (1:ℝ) * bernsteinWeight 1 i 0 * bernsteinWeight 2 j 1 :=
  bernstein_two_positive_blend (fun _ _ => 1) (by intros; norm_num)
    0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Deleting the outer factor four changes the represented rational gap.
example : singletonClearedNumerator 1 1 1 1 0 0 1 ≠
    (16:ℝ)^4 * (singletonEntry 1 1 0 * singletonMinorFloor 1 1 1 0 0 - 24/625) := by
  norm_num [singletonClearedNumerator, singletonEntry, singletonMinorFloor]

-- The cap comparison includes the degenerate triangle vertex and its opposite edge.
example : smallBlockFloor 0 0 ≤ smallBlockFloorAt 0 0 0 :=
  smallBlockFloor_le_actual (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : largeBlockFloor (13/50) 0 ≤ largeBlockFloorAt (13/50) 0 (13/50) :=
  largeBlockFloor_le_actual (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms bernstein_two_positive_blend
#print axioms blockPowerCoefficients_pos
#print axioms singleton_cleared_identity
#print axioms eval_singletonPolynomial
#print axioms singleton_normalized_gap
#print axioms singleton_gap_of_crossing_le
#print axioms smallBlockFloor_le_actual
#print axioms largeBlockFloor_le_actual
