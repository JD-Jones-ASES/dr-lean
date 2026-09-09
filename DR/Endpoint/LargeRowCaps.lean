import DR.Endpoint.Caps
import DR.Endpoint.FactorialDecay
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact column cap for the m≥128 endpoint strips, plus the initial row lower bound. -/

namespace DittertRybin

/-- The elementary variance radius is below m⁻⁴ throughout the accepted large-m domain. -/
theorem endpoint_column_radius_lt_inv_fourth {m : ℕ} (hm : 128 ≤ m) :
    Real.sqrt (2*dittertConstant m/((m:ℝ)*(1-dittertConstant m))) < 1/(m:ℝ)^4 := by
  have hmR : (128:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have ha0 := endpoint_a_pos (by omega : 0 < m)
  have ha1 := endpoint_a_lt_one (by omega : 2 ≤ m)
  have hdec := distinctUniformProbability_endpoint_le_inv_fourteenth hm
  rw [distinctUniformProbability_self] at hdec
  have hp14 : (3:ℝ) ≤ (m:ℝ)^14 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 128) hmR 14
    norm_num at h
    linarith
  have ha3 : dittertConstant m ≤ 1/3 := hdec.trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp14)
  have hA : 2*dittertConstant m/((m:ℝ)*(1-dittertConstant m)) ≤
      3*dittertConstant m/(m:ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hm0 (sub_pos.mpr ha1)) hm0).mpr
    nlinarith [mul_nonneg (mul_nonneg hm0.le ha0.le) (show 0 ≤ 1-3*dittertConstant m by linarith)]
  have hB : 3*dittertConstant m/(m:ℝ) ≤ 3/(m:ℝ)^15 := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdec (by norm_num : (0:ℝ) ≤ 3)) hm0.le
    convert h using 1 <;> first | rfl | field_simp
  have hp7 : (3:ℝ) < (m:ℝ)^7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 128) hmR 7
    norm_num at h
    linarith
  have hC : 3/(m:ℝ)^15 < (1/(m:ℝ)^4)^2 := by
    apply (div_lt_iff₀ (pow_pos hm0 15)).mpr
    have he : (1/(m:ℝ)^4)^2*(m:ℝ)^15 = (m:ℝ)^7 := by field_simp
    rw [he]
    exact hp7
  have h := (hA.trans hB).trans_lt hC
  exact (Real.sqrt_lt' (by positivity : 0 < 1/(m:ℝ)^4)).mpr h

theorem endpoint_contender_column_cap_large {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (j : Fin n) :
    colSum P j < 1/(n:ℝ)+1/(m:ℝ)^4 :=
  (endpoint_contender_column_cap (by omega) hmn hP hcont j).trans_lt
    (add_lt_add_right (endpoint_column_radius_lt_inv_fourth hm) _)

/-- The lower row cap used before any LLL estimate; no lower bound for p_original is assumed. -/
theorem endpoint_contender_scaled_row_lower_third {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (i : Fin m) :
    (1-distinctUniformProbability n m)/3 < (m:ℝ)*rowSum P i := by
  have h := endpoint_contender_scaled_row_lower hm hmn hP hcont i
  have hy := mul_pos (show (0:ℝ) < m by exact_mod_cast (by omega : 0 < m))
    (endpoint_contender_rows_pos hm hmn hP hcont i)
  have hmul := (div_le_iff₀ (Real.exp_pos 1)).mp h
  have hexp := mul_lt_mul_of_pos_left Real.exp_one_lt_three hy
  nlinarith

end DittertRybin
