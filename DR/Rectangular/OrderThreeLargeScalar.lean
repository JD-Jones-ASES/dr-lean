import DR.Rectangular.OrderThreeLargeBounds
import Mathlib.Tactic.Positivity

/-! Exact scalar inequalities behind the three-sample near/far decomposition. -/

namespace DittertRybin

/-- Homogeneous tangent bound for the mixed cubic; the cell energy remains explicit. -/
theorem orderThree_mixed_tangent (E T A B W C : ℝ)
    (hE : 0 < E) (hT : 0 ≤ T) (hTE : T ≤ E)
    (hCS : C ^ 2 ≤ (E - T) * A * B)
    (hAB : 4 * A * B ≤ W * T ^ 2) (hsize : W * E ≤ 2) :
    -(3 / 4 * E + 3 / 2 * T) ≤ 6 * C := by
  have hET : 0 ≤ E - T := sub_nonneg.mpr hTE
  have h1 := mul_le_mul_of_nonneg_left hCS (show 0 ≤ 36 * E by linarith)
  have h2 := mul_le_mul_of_nonneg_left hAB
    (show 0 ≤ 9 * E * (E - T) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 9 * (E - T) * T ^ 2 by positivity)
  have h4 : 18 * (E - T) * T ^ 2 ≤ E * (3 / 4 * E + 3 / 2 * T) ^ 2 := by
    have hp := mul_nonneg (sq_nonneg (2 * T - E)) (show 0 ≤ 8 * T + E by linarith)
    nlinarith
  have hs : E * (6 * C) ^ 2 ≤ E * (3 / 4 * E + 3 / 2 * T) ^ 2 := by
    nlinarith
  have hs' : (6 * C) ^ 2 ≤ (3 / 4 * E + 3 / 2 * T) ^ 2 :=
    le_of_mul_le_mul_left hs hE
  exact (abs_le_of_sq_le_sq' hs' (by linarith)).1

/-- A squared linear bound gives the exact quadratic completion, including T=0. -/
theorem orderThree_quadratic_completion (E T C d L : ℝ)
    (hC : 0 < C) (hd : 0 < d) (hL : L ^ 2 ≤ C * T) :
    -9 * C / d * E ^ 2 ≤ d * T - 6 * L * E := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h1 := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hL)
  have h2 := sq_nonneg (d * L - 3 * C * E)
  have hsum : 0 ≤ d ^ 2 * C * T - 6 * d * C * L * E + 9 * C ^ 2 * E ^ 2 := by
    nlinarith
  have heq : C * d * (d * T - 6 * L * E + 9 * C / d * E ^ 2) =
      d ^ 2 * C * T - 6 * d * C * L * E + 9 * C ^ 2 * E ^ 2 := by
    field_simp
  have hscaled : C * d * 0 ≤ C * d * (d * T - 6 * L * E + 9 * C / d * E ^ 2) := by
    simpa only [mul_zero, heq] using hsum
  have hnonneg : 0 ≤ d * T - 6 * L * E + 9 * C / d * E ^ 2 :=
    le_of_mul_le_mul_left hscaled (mul_pos hC hd)
  simp only [div_eq_mul_inv] at hnonneg ⊢
  nlinarith

theorem orderThree_near_scalar (E T C W d c G : ℝ)
    (hE : 0 ≤ E) (hT : 0 ≤ T) (hC : 0 < C) (hW : 0 < W) (hd : 0 < d)
    (hsize : W * E ≤ 2)
    (hG : (c - 3 / 4) * E + d * T - 6 * Real.sqrt (C * T) * E ≤ G) :
    (c - 3 / 4 - 18 * (C / W) / d) * E ≤ G := by
  have hroot : Real.sqrt (C * T) ^ 2 ≤ C * T :=
    (Real.sq_sqrt (mul_nonneg hC.le hT)).le
  have hyoung := orderThree_quadratic_completion E T C d (Real.sqrt (C * T)) hC hd hroot
  have hcap : E ≤ 2 / W := (le_div_iff₀ hW).mpr (by nlinarith)
  have hproduct := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 9 * C / d * E by positivity)
  have hbound : 9 * C / d * E ^ 2 ≤ 18 * (C / W) / d * E := by
    calc
      9 * C / d * E ^ 2 = 9 * C / d * E * E := by ring
      _ ≤ 9 * C / d * E * (2 / W) := hproduct
      _ = 18 * (C / W) / d * E := by ring
  simp only [div_eq_mul_inv] at hyoung hG hbound ⊢
  nlinarith

/-- Monotonicity of 3s-2s^(3/2) on the entire probability second-moment interval. -/
theorem orderThree_far_function_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    3 * a - 2 * a * Real.sqrt a ≤ 3 * b - 2 * b * Real.sqrt b := by
  have hb0 := ha.trans hab
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hxy := Real.sqrt_le_sqrt hab
  have hy1 : Real.sqrt b ≤ 1 := by simpa using Real.sqrt_le_sqrt hb
  have hx1 := hxy.trans hy1
  have hxsq := Real.sq_sqrt ha
  have hysq := Real.sq_sqrt hb0
  have hxx := mul_nonneg hx (sub_nonneg.mpr hx1)
  have hyy := mul_nonneg hy (sub_nonneg.mpr hy1)
  have hxy1 := mul_nonneg hx (sub_nonneg.mpr hy1)
  have hyx1 := mul_nonneg hy (sub_nonneg.mpr hx1)
  have hbracket : 0 ≤ 3 * (Real.sqrt a + Real.sqrt b) -
      2 * (Real.sqrt a ^ 2 + Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2) := by
    nlinarith
  have hfactor := mul_nonneg (sub_nonneg.mpr hxy) hbracket
  have hau : Real.sqrt a ^ 3 = a * Real.sqrt a := by rw [pow_succ, hxsq]
  have hbv : Real.sqrt b ^ 3 = b * Real.sqrt b := by rw [pow_succ, hysq]
  nlinarith

end DittertRybin
