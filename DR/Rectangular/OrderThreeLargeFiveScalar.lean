import DR.Rectangular.OrderThreeLargeScalar

/-! The exact one-variable certificate for the five-row infinite strip. -/

namespace DittertRybin

noncomputable def orderThreeFiveExpression (n u : ℝ) : ℝ :=
  (9 / 5 - 22 / (5 * n)) + (18 / 5) * u ^ 2 - (6 * Real.sqrt 8 / 5) * u -
    (3 / (1 - 2 / n)) *
      (u ^ 2 * (1 - u ^ 2) + 2 * u * Real.sqrt (1 - u ^ 2) / Real.sqrt n + 1 / n)

theorem orderThreeFiveExpression_lower {n u : ℝ} (hn : 121 ≤ n) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (27197 / 2772275 : ℝ) ≤ orderThreeFiveExpression n u := by
  have hn0 : 0 < n := by linarith
  have hni : 1 / n ≤ 1 / 121 := one_div_le_one_div_of_le (by norm_num) hn
  have hsqrt : 11 ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hn
    have h121 : Real.sqrt (121 : ℝ) = 11 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    simpa only [h121] using h
  have hri : 1 / Real.sqrt n ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) hsqrt
  have hden : 119 / 121 ≤ 1 - 2 / n := by
    simp only [div_eq_mul_inv] at hni ⊢
    nlinarith
  have hden0 : 0 < 1 - 2 / n := by linarith
  have hT : 3 / (1 - 2 / n) ≤ 363 / 119 := by
    apply (div_le_iff₀ hden0).mpr
    linarith
  have hc : 97 / 55 ≤ 9 / 5 - 22 / (5 * n) := by
    simp only [div_eq_mul_inv, mul_inv_rev] at hni ⊢
    nlinarith
  have huSq : 0 ≤ 1 - u ^ 2 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hw := Real.sqrt_nonneg (1 - u ^ 2)
  have hwSq := Real.sq_sqrt huSq
  have hcross : 2 * u * Real.sqrt (1 - u ^ 2) ≤ 1 := by
    nlinarith [sq_nonneg (u - Real.sqrt (1 - u ^ 2))]
  have hcrossBound : 2 * u * Real.sqrt (1 - u ^ 2) / Real.sqrt n ≤ 1 / 11 :=
    (div_le_div_of_nonneg_right hcross (Real.sqrt_nonneg n)).trans hri
  have hpoly : u ^ 2 * (1 - u ^ 2) ≤ (1 / 5) * u ^ 2 + 4 / 25 := by
    nlinarith [sq_nonneg (u ^ 2 - 2 / 5)]
  have hbracket : u ^ 2 * (1 - u ^ 2) + 2 * u * Real.sqrt (1 - u ^ 2) / Real.sqrt n + 1 / n ≤
      (1 / 5) * u ^ 2 + 4 / 25 + 12 / 121 := by linarith
  have hb0 : 0 ≤ u ^ 2 * (1 - u ^ 2) + 2 * u * Real.sqrt (1 - u ^ 2) / Real.sqrt n + 1 / n := by
    positivity
  have hproduct := mul_le_mul hT hbracket hb0 (by norm_num : (0 : ℝ) ≤ 363 / 119)
  have hpre : 4549 / 4675 + (1779 / 595) * u ^ 2 - (6 * Real.sqrt 8 / 5) * u ≤
      orderThreeFiveExpression n u := by
    unfold orderThreeFiveExpression
    nlinarith
  have hfinal : (27197 / 2772275 : ℝ) ≤
      4549 / 4675 + (1779 / 595) * u ^ 2 - (6 * Real.sqrt 8 / 5) * u := by
    have h8 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith [sq_nonneg (2 * (1779 / 595) * u - 6 * Real.sqrt 8 / 5)]
  exact hfinal.trans hpre

end DittertRybin
