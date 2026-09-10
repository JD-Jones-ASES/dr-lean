import DR.Endpoint.DoubleWeights

/-! The exact all-dimension scalar criterion on m≤n≤2m, beginning at m=117.
The sole literal base is followed by proved recurrences and column monotonicity. -/

namespace DittertRybin

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem endpoint_near_square_parameter_base :
    endpointDoubleBoundarySum 5 117 < (39/40 : ℝ)*(128/289) := by
  norm_num [endpointDoubleBoundarySum, distinctUniformProbability, dittertConstant,
    Nat.descFactorial, Nat.factorial]

theorem endpoint_near_square_double_sum_lt {m : ℕ} (hm : 117 ≤ m) :
    endpointDoubleBoundarySum 5 m < (128/289 : ℝ) := by
  have h := endpointDoubleBoundarySum_le_base (p := 5) (by decide : 80 ≤ 117) hm (by decide)
  exact (h.trans_lt endpoint_near_square_parameter_base).trans (by norm_num)

/-- The criterion with gain one, on the entire accepted near-square interval. -/
theorem endpoint_near_square_parameter_criterion {m n : ℕ}
    (hm : 117 ≤ m) (hmn : m ≤ n) (hn : n ≤ 2*m) :
    distinctUniformProbability n m + ((n : ℝ)-1)*dittertConstant m <
      (512/289 : ℝ) / ((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2) := by
  have hmR : (117 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnR : (n : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have hM1 : 0 ≤ 2*(m : ℝ)-1 := by linarith
  have ha : 0 ≤ dittertConstant m := (endpoint_a_pos (by omega)).le
  have hb : 0 ≤ distinctUniformProbability n m := (distinctUniformProbability_pos (by omega) hmn).le
  have hbmono := distinctUniformProbability_mono_columns (by omega : 0 < n) hmn hn
  have hbN : 0 ≤ distinctUniformProbability (2*m) m := hb.trans hbmono
  have hprod : (distinctUniformProbability n m + ((n : ℝ)-1)*dittertConstant m) *
      ((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2) ≤
      (distinctUniformProbability (2*m) m + (2*(m : ℝ)-1)*dittertConstant m) *
      ((m : ℝ)^3*(2*(m : ℝ))^2*(2*(m : ℝ)-1)^2) := by
    gcongr
  have heq : (distinctUniformProbability (2*m) m + (2*(m : ℝ)-1)*dittertConstant m) *
      ((m : ℝ)^3*(2*(m : ℝ))^2*(2*(m : ℝ)-1)^2) =
      4*endpointDoubleBoundarySum 5 m := by
    unfold endpointDoubleBoundarySum
    ring
  apply (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2)).mpr
  rw [heq] at hprod
  have hsum := endpoint_near_square_double_sum_lt hm
  linarith

end DittertRybin
