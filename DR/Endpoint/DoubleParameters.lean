import DR.Endpoint.DoubleWeights

/-! The exact arithmetic-gain scalar criterion for m×2m, beginning at m=80.
The row-count gain is m, so the common weighted recurrence has exponent three. -/

namespace DittertRybin

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem endpoint_double_parameter_base :
    endpointDoubleBoundarySum 3 80 < (91/100 : ℝ)*(128/289) := by
  norm_num [endpointDoubleBoundarySum, distinctUniformProbability, dittertConstant,
    Nat.descFactorial, Nat.factorial]

theorem endpoint_double_sum_lt {m : ℕ} (hm : 80 ≤ m) :
    endpointDoubleBoundarySum 3 m < (128/289 : ℝ) := by
  have h := endpointDoubleBoundarySum_le_base (p := 3) (le_refl 80) hm (by decide)
  exact (h.trans_lt endpoint_double_parameter_base).trans (by norm_num)

/-- The criterion with the full arithmetic gain m at every accepted doubled dimension. -/
theorem endpoint_double_parameter_criterion {m : ℕ} (hm : 80 ≤ m) :
    distinctUniformProbability (2*m) m + (((2*m : ℕ) : ℝ)-1)*dittertConstant m <
      (512/289 : ℝ)*(m : ℝ)^2 /
        ((m : ℝ)^3*((2*m : ℕ) : ℝ)^2*(((2*m : ℕ) : ℝ)-1)^2) := by
  have hmR : (80 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : 0 < 2*(m : ℝ)-1 := by linarith
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply (lt_div_iff₀ (by positivity :
    0 < (m : ℝ)^3*(2*(m : ℝ))^2*(2*(m : ℝ)-1)^2)).mpr
  have heq : (distinctUniformProbability (2*m) m + (2*(m : ℝ)-1)*dittertConstant m) *
      ((m : ℝ)^3*(2*(m : ℝ))^2*(2*(m : ℝ)-1)^2) =
      (4*(m : ℝ)^2)*endpointDoubleBoundarySum 3 m := by
    unfold endpointDoubleBoundarySum
    ring
  rw [heq]
  have h := mul_lt_mul_of_pos_left (endpoint_double_sum_lt hm)
    (by positivity : 0 < 4*(m : ℝ)^2)
  nlinarith only [h]

end DittertRybin
