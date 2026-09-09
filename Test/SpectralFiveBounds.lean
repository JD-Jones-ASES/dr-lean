import DR.Certificates.SpectralFiveTwoBlockBounds

namespace DittertRybin.Tests
open Certificates.SpectralFiveTwoBlocks

-- The triangular normalization retains the degenerate right-hand edge.
example : ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
    (13 / 50 : ℝ) = (13 / 50) * x ∧ 0 = (13 / 50) * (1 - x) * y :=
  triangle_unit_coordinates (by norm_num) (by norm_num) (by norm_num)

-- The loose 9/20 crossing estimate is insufficient for the same product argument.
example :
    (2 - (9 / 20 : ℝ) / (2 * (79 / 100)) - (9 / 20) / 2 - (3 / 2) * (1 - (9 / 20) / 4) ^ 2) *
    (2 - (9 / 20 : ℝ) / 2 - (9 / 20) / (2 * (79 / 100)) - (16 / 9) * (1 - (9 / 20) / 6) ^ 3) < 24 / 625 := by
  norm_num

#print axioms triangle_unit_coordinates
#print axioms two_block_scalar_conditions
#print axioms two_block_floor_gap
end DittertRybin.Tests
