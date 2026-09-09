import DR.Rectangular.OrderThreeLargeExpansion
import DR.Rectangular.OrderThreeLargeScalar

/-! The far-from-uniform region for three samples, on every rectangle with both dimensions at least three. -/

namespace DittertRybin
open scoped BigOperators

/-- The failure polynomial splits into repeated-cell and nonnegative L-shape terms. -/
theorem orderThreeFailurePolynomial_lshape {m n : ℕ} (P : Board m n) :
    orderThreeFailurePolynomial P =
      3 * totalMass P * orderThreeSquareSum P - 2 * (∑ i, ∑ j, P i j ^ 3) +
      6 * (∑ i, ∑ j, P i j * (rowSum P i - P i j) * (colSum P j - P i j)) := by
  have hp (i : Fin m) (j : Fin n) :
      P i j * (rowSum P i - P i j) * (colSum P j - P i j) =
        P i j * rowSum P i * colSum P j - P i j ^ 2 * (rowSum P i + colSum P j) + P i j ^ 3 := by ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    orderThreeFailurePolynomial, orderThreeSquareSum]
  ring

theorem orderThreeFailurePolynomial_lower_secondMoment {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) :
    3 * orderThreeSquareSum P - 2 * orderThreeSquareSum P * Real.sqrt (orderThreeSquareSum P) ≤
      orderThreeFailurePolynomial P := by
  have hL : 0 ≤ ∑ i, ∑ j, P i j * (rowSum P i - P i j) * (colSum P j - P i j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have hr : P i j ≤ rowSum P i :=
      Finset.single_le_sum (fun k _ => hP.1 i k) (Finset.mem_univ j)
    have hc : P i j ≤ colSum P j :=
      Finset.single_le_sum (fun k _ => hP.1 k j) (Finset.mem_univ i)
    exact mul_nonneg (mul_nonneg (hP.1 i j) (sub_nonneg.mpr hr)) (sub_nonneg.mpr hc)
  rw [orderThreeFailurePolynomial_lshape, hP.2]
  nlinarith [orderThree_cube_upper P]

/-- The far-region gap is strict even at the smallest allowed area. -/
theorem orderThree_far_gap_scalar (h s : ℝ) (hh : 0 < h) (hcap : h ≤ 1 / 9)
    (hs : 2 * Real.sqrt h ≤ s) :
    9 * h - 6 * h * s + 4 * h ^ 2 < 9 * h - 6 * h * Real.sqrt (3 * h) := by
  have hz := Real.sqrt_pos.mpr hh
  have hzsq := Real.sq_sqrt hh.le
  have hzcap : Real.sqrt h ≤ 1 / 3 := by nlinarith
  have hzh : 3 * h ≤ Real.sqrt h := by
    nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hzcap)]
  have h3nonneg := Real.sqrt_nonneg (3 : ℝ)
  have h3sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h3 : Real.sqrt (3 : ℝ) < 16 / 9 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right h3 hz
  have hroot : Real.sqrt (3 * h) < s - 2 / 3 * h := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hroot (show 0 < 6 * h by positivity)
  nlinarith

theorem orderThree_squareSum_centered {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    orderThreeSquareSum P = ((m : ℝ) * n)⁻¹ + orderThreeSquareSum (orderThreeCentered P) := by
  rw [orderThreeCentered_squareSum]
  simpa only [cellSquareSum, Fintype.sum_prod_type, orderThreeSquareSum] using
    cellSquareSum_eq_uniform_add_variance hm hn hP

/-- Strict optimality throughout the far region, with no support or marginal restrictions. -/
theorem orderThreeFailurePolynomial_far {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hfar : 2 * ((m : ℝ) * n)⁻¹ ≤ orderThreeSquareSum (orderThreeCentered P)) :
    orderThreeFailurePolynomial (uniformBoard m n) < orderThreeFailurePolynomial P := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : (0 : ℝ) < (m : ℝ) * n := by positivity
  have hh : 0 < ((m : ℝ) * n)⁻¹ := inv_pos.mpr hprod
  have hprod9 : (9 : ℝ) ≤ (m : ℝ) * n := by nlinarith
  have hcap : ((m : ℝ) * n)⁻¹ ≤ 1 / 9 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hprod9
  have hsnonneg : 0 ≤ (m : ℝ)⁻¹ + (n : ℝ)⁻¹ := by positivity
  have hssq : (2 * Real.sqrt (((m : ℝ) * n)⁻¹)) ^ 2 ≤
      ((m : ℝ)⁻¹ + (n : ℝ)⁻¹) ^ 2 := by
    rw [mul_inv]
    have hsq := Real.sq_sqrt hh.le
    rw [mul_inv] at hsq
    nlinarith [sq_nonneg ((m : ℝ)⁻¹ - (n : ℝ)⁻¹)]
  have hs := le_of_sq_le_sq hssq hsnonneg
  have hmoment := orderThree_squareSum_centered hm0 hn0 hP
  have hlow : 3 * ((m : ℝ) * n)⁻¹ ≤ orderThreeSquareSum P := by linarith
  have hmono := orderThree_far_function_mono (3 * ((m : ℝ) * n)⁻¹)
    (orderThreeSquareSum P) (by positivity) hlow (orderThree_probability_squareSum_le_one hP)
  have hgap := orderThree_far_gap_scalar (((m : ℝ) * n)⁻¹)
    ((m : ℝ)⁻¹ + (n : ℝ)⁻¹) hh hcap hs
  rw [orderThreeFailurePolynomial_uniform hm0 hn0]
  have hQ := orderThreeFailurePolynomial_lower_secondMoment hP
  nlinarith

end DittertRybin
