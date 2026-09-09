import DR.Rectangular.OrderThreeLargeFiveBounds

/-! Exact elimination of the column energy for the five-row strip. -/

namespace DittertRybin
open scoped BigOperators

/-- The five-row estimate before normalizing the remaining row direction. -/
theorem orderThreeFailurePolynomial_five_prebound {n : ℕ} (hn : 3 ≤ n)
    {P : Board 5 n} (hP : IsProbability P) :
    let X := orderThreeCentered P
    let E := orderThreeSquareSum X
    let A := orderThreeRowSquareSum X
    (9 / 5 - 22 / (5 * (n : ℝ))) * E + (18 / 5) * (A / n) -
      6 * Real.sqrt ((4 / 5) * A) * E -
      9 * (Real.sqrt ((E - A / n) * A) + E) ^ 2 /
        (6 * ((5 : ℝ) * n)⁻¹ * ((n : ℝ) - 2)) ≤
      orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard 5 n) := by
  let X := orderThreeCentered P
  let E := orderThreeSquareSum X
  let A := orderThreeRowSquareSum X
  let B := orderThreeColSquareSum X
  let R := Real.sqrt ((E - A / n) * A)
  let D := 6 * ((5 : ℝ) * n)⁻¹ * ((n : ℝ) - 2)
  have hn0 : 0 < n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnne := ne_of_gt hnpos
  have hnsub : 0 < (n : ℝ) - 2 := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hX : totalMass X = 0 := orderThreeCentered_totalMass (by norm_num) hn0 hP
  have hB : 0 ≤ B := orderThreeColSquareSum_nonneg X
  have hmixed := orderThree_mixed_lower_row_residual (by norm_num : 0 < 5) hn0 X hX
  have hlinear := orderThree_linear_upper_refined (by norm_num : 0 < 5) X hX
  norm_num only [Nat.cast_ofNat, show (5 - 1 : ℝ) = 4 by norm_num] at hlinear
  change -R * Real.sqrt B ≤ orderThreeMixedMoment X at hmixed
  change orderThreeLinearMoment X ≤ (Real.sqrt ((4 / 5) * A) + Real.sqrt B) * E at hlinear
  have hcompletion := orderThree_sqrt_completion B D (R + E) hB hD
  have hcube : -((5 : ℝ) * n)⁻¹ * E ≤ ∑ i, ∑ j, X i j ^ 3 := by
    apply orderThree_cube_lower
    intro i j
    dsimp [X, orderThreeCentered, uniformBoard]
    linarith [hP.1 i j]
  have hexp := orderThreeFailurePolynomial_centered (by norm_num : 0 < 5) hn0 hP
  change orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard 5 n) =
    3 * ((5 : ℝ) * n)⁻¹ * (5 - 2) * ((n : ℝ) - 2) * E +
    6 * ((5 : ℝ) * n)⁻¹ * (5 - 2) * A + D * B +
    4 * (∑ i, ∑ j, X i j ^ 3) + 6 * orderThreeMixedMoment X - 6 * orderThreeLinearMoment X at hexp
  have hcoef : 3 * ((5 : ℝ) * n)⁻¹ * (5 - 2) * ((n : ℝ) - 2) * E +
      6 * ((5 : ℝ) * n)⁻¹ * (5 - 2) * A - 4 * ((5 : ℝ) * n)⁻¹ * E =
      (9 / 5 - 22 / (5 * (n : ℝ))) * E + (18 / 5) * (A / n) := by
    field_simp
    ring
  change (9 / 5 - 22 / (5 * (n : ℝ))) * E + (18 / 5) * (A / n) -
    6 * Real.sqrt ((4 / 5) * A) * E - 9 * (R + E) ^ 2 / D ≤ _
  simp only [div_eq_mul_inv] at hcompletion hcoef ⊢
  nlinarith

end DittertRybin
