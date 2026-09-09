import DR.Square.FiveSweepCut
import DR.Square.HomogeneousDittert
import DR.Certificates.SpectralFiveSingletonCoordinates

/-! Exact controls for score-cut ordering and homogeneous minor normalization. -/

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates.SpectralFiveSingleton

-- Arbitrary rectangular zero-mass support is forced to be the zero matrix.
example (m n : ℕ) (A : Board m n) (hA : ∀ i j, 0 ≤ A i j)
    (hm : totalMass A = 0) : A = 0 := board_eq_zero_of_nonneg_mass_zero A hA hm

-- Order two applies directly to zero mass, with no normalization by zero assumed.
example : dittertFunctional (0 : Board 2 2) ≤
    (2-dittertConstant 2) * (totalMass (0 : Board 2 2)/2)^2 :=
  dittert_order_two.homogeneous (by norm_num) 0 (by intros; simp)

-- Using n squared instead of n for block-mass normalization is false.
example : ¬ ((∏ i, rowSum ((3:ℝ) • (1:Board 2 2)) i) +
      (∏ j, colSum ((3:ℝ) • (1:Board 2 2)) j) -
      (2-dittertConstant 2) * (totalMass ((3:ℝ) • (1:Board 2 2))/4)^2 ≤
      ((3:ℝ) • (1:Board 2 2)).permanent) := by
  norm_num [rowSum, colSum, totalMass, dittertConstant, Nat.factorial,
    Fin.sum_univ_two, Fin.prod_univ_two, Matrix.permanent_smul]

-- The collapsed t=0 box is represented exactly.
example : ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
    0 = (23/50)*0*x ∧ 0 = (1/2)*0*y :=
  singleton_unit_coordinates (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms ordered_subset_sum_le_card
#print axioms LowerMarginalCut.complementary_row_floor
#print axioms LowerMarginalCut.chosen_col_floor
#print axioms dittert_globalMax_cut_five
#print axioms DittertMaximizer.homogeneous
#print axioms DittertMaximizer.permanent_lower
#print axioms singleton_unit_coordinates

end DittertRybin.Tests
