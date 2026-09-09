import DR.Rectangular.OrderThreeLargeFar
import DR.Rectangular.OrderThreeLargeDimensions

/-! Quantitative near-uniform control on the full probability simplex. -/

namespace DittertRybin
open scoped BigOperators

theorem orderThree_marginal_quadratic_lower {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≤ n) (X : Board m n) :
    (6 - 12 / (m : ℝ)) * orderThreeMarginalSquareSum X ≤
      6 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * orderThreeRowSquareSum X +
      6 * (((m : ℝ) * n)⁻¹) * ((n : ℝ) - 2) * orderThreeColSquareSum X := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have heq : 6 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * orderThreeRowSquareSum X +
      6 * (((m : ℝ) * n)⁻¹) * ((n : ℝ) - 2) * orderThreeColSquareSum X -
      (6 - 12 / (m : ℝ)) * orderThreeMarginalSquareSum X =
      12 * ((n : ℝ) - m) * orderThreeColSquareSum X / ((m : ℝ) ^ 2 * n) := by
    unfold orderThreeMarginalSquareSum
    field_simp
    ring
  have hp := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (sub_nonneg.mpr hmnR))
      (orderThreeColSquareSum_nonneg X))
    (mul_nonneg (sq_nonneg (m : ℝ)) (Nat.cast_nonneg n))
  linarith

/-- Exact retained aspect-ratio bound; no strict positivity is assumed of any cell. -/
theorem orderThreeFailurePolynomial_near {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hnear : orderThreeSquareSum (orderThreeCentered P) ≤ 2 * ((m : ℝ) * n)⁻¹) :
    orderThreeLargeCriterion m n * orderThreeSquareSum (orderThreeCentered P) ≤
      orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := lt_of_lt_of_le hm0 hmn
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmne := ne_of_gt hmpos
  have hnne := ne_of_gt hnpos
  let X := orderThreeCentered P
  let E := orderThreeSquareSum X
  let T := orderThreeMarginalSquareSum X
  let A := orderThreeRowSquareSum X
  let B := orderThreeColSquareSum X
  let W : ℝ := (m : ℝ) * n
  let C : ℝ := (m : ℝ) + n
  let c : ℝ := 3 - 6 / m - 6 / n + 8 / W
  let d : ℝ := 9 / 2 - 12 / m
  have hX : totalMass X = 0 := orderThreeCentered_totalMass hm0 hn0 hP
  have hE0 : 0 ≤ E := orderThreeSquareSum_nonneg X
  by_cases hEz : E = 0
  · have hXz : X = 0 := (orderThreeSquareSum_eq_zero_iff X).mp hEz
    have hU := (orderThreeCentered_eq_zero_iff P).mp hXz
    change orderThreeLargeCriterion m n * E ≤ _
    rw [hEz, mul_zero, hU, sub_self]
  have hE : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEz)
  have hT : 0 ≤ T := orderThreeMarginalSquareSum_nonneg X
  have hTE : T ≤ E := orderThreeMarginalSquareSum_le hm0 hn0 X hX
  have hW : 0 < W := mul_pos hmpos hnpos
  have hC : 0 < C := add_pos hmpos hnpos
  have hd : 0 < d := by
    have hrecip : (1 : ℝ) / m ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hmR
    dsimp [d]
    simp only [div_eq_mul_inv] at hrecip ⊢
    nlinarith
  have hsize : W * E ≤ 2 := by
    calc
      W * E ≤ W * (2 * W⁻¹) := mul_le_mul_of_nonneg_left hnear hW.le
      _ = 2 := by field_simp
  have hmixed := orderThree_mixed_tangent E T A B W (orderThreeMixedMoment X)
    hE hT hTE (orderThree_mixed_sq_le hm0 hn0 X hX)
    (orderThree_marginal_product_le hm0 hn0 X) hsize
  have hlinear := orderThree_linear_upper hm0 hn0 X
  have hcube : -W⁻¹ * E ≤ ∑ i, ∑ j, X i j ^ 3 := by
    apply orderThree_cube_lower
    intro i j
    dsimp [X, orderThreeCentered, uniformBoard, W]
    linarith [hP.1 i j]
  have hrows := orderThree_marginal_quadratic_lower hm0 hn0 hmn X
  have hexp := orderThreeFailurePolynomial_centered hm0 hn0 hP
  have hecoef : 3 * W⁻¹ * ((m : ℝ) - 2) * ((n : ℝ) - 2) * E - 4 * W⁻¹ * E = c * E := by
    dsimp [W, c]
    field_simp
    ring
  have hG : (c - 3 / 4) * E + d * T - 6 * Real.sqrt (C * T) * E ≤
      orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) := by
    change (c - 3 / 4) * E + (9 / 2 - 12 / (m : ℝ)) * T -
      6 * Real.sqrt (((m : ℝ) + n) * T) * E ≤ _
    change 6 * W⁻¹ * ((m : ℝ) - 2) * A + 6 * W⁻¹ * ((n : ℝ) - 2) * B ≥
      (6 - 12 / (m : ℝ)) * T at hrows
    change orderThreeLinearMoment X ≤ Real.sqrt (((m : ℝ) + n) * T) * E at hlinear
    change orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) =
      3 * W⁻¹ * ((m : ℝ) - 2) * ((n : ℝ) - 2) * E +
      6 * W⁻¹ * ((m : ℝ) - 2) * A + 6 * W⁻¹ * ((n : ℝ) - 2) * B +
      4 * (∑ i, ∑ j, X i j ^ 3) + 6 * orderThreeMixedMoment X - 6 * orderThreeLinearMoment X at hexp
    nlinarith
  have hfinal := orderThree_near_scalar E T C W d c
    (orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n))
    hE0 hT hC hW hd hsize hG
  have hcoef : c - 3 / 4 - 18 * (C / W) / d = orderThreeLargeCriterion m n := by
    dsimp [c, C, W, d, orderThreeLargeCriterion]
    have hrec : ((m : ℝ) + n) / ((m : ℝ) * n) = 1 / (m : ℝ) + 1 / (n : ℝ) := by
      field_simp
      ring
    rw [hrec]
  rw [hcoef] at hfinal
  exact hfinal

end DittertRybin
