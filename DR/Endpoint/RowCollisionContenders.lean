import DR.Endpoint.RowCollisionBounds
import DR.Endpoint.RowCollisionUnion
import DR.Endpoint.LargeRowCaps

/-! Original-row collision inputs derived solely from an actual endpoint
contender. These are the quantitative inputs to the transition-strip LLL
argument, not a replacement for that avoidance estimate. -/

namespace DittertRybin
open scoped BigOperators

/-- The contender's exact column cap supplies the normalized total collision estimate. -/
theorem endpoint_original_collisionIntensity_large {m n : ℕ}
    (hm : 128 ≤ m) (hmn : m ≤ n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    rowCollisionIntensity (normalizeRows P) ≤
      (1/(n:ℝ)+1/(m:ℝ)^4)*(m:ℝ)^2/2*
        (1+endpointRowReciprocalDeviation P/(m:ℝ)) :=
  endpoint_original_collisionIntensity_le (by omega) hmn hP hcont
    (fun j => (endpoint_contender_column_cap_large hm hmn hP hcont j).le)

/-- An explicit graph-load bound before an LLL or other avoidance estimate. -/
theorem endpoint_original_collisionLoad_large {m n : ℕ}
    (hm : 128 ≤ m) (hmn : m ≤ n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (i : Fin m) :
    rowCollisionLoad (normalizeRows P) i ≤
      3*(m:ℝ)*(1/(n:ℝ)+1/(m:ℝ)^4)/(1-distinctUniformProbability n m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hb : distinctUniformProbability n m < 1 :=
    distinctUniformProbability_lt_one (by omega) (by omega)
  have hrmin : 0 < (1-distinctUniformProbability n m)/(3*(m:ℝ)) :=
    div_pos (sub_pos.mpr hb) (mul_pos (by norm_num) hm0)
  have hr (u : Fin m) : (1-distinctUniformProbability n m)/(3*(m:ℝ)) ≤ rowSum P u := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hm0)).mpr
    have h := endpoint_contender_scaled_row_lower_third (by omega) hmn hP hcont u
    linarith
  have h := normalizedRow_collisionLoad_le P hP.1 hrmin hr
    (fun j => (endpoint_contender_column_cap_large hm hmn hP hcont j).le) i
  apply h.trans_eq
  field_simp

/-- The elementary lower bound belongs to the original normalized-row law. -/
theorem endpoint_original_avoidance_lower_union {m n : ℕ}
    (hm : 128 ≤ m) (hmn : m ≤ n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    1-(1/(n:ℝ)+1/(m:ℝ)^4)*(m:ℝ)^2/2*
      (1+endpointRowReciprocalDeviation P/(m:ℝ)) ≤ originalRowAvoidance P := by
  have hr := endpoint_contender_rows_pos (by omega) hmn hP hcont
  have hU := one_sub_rowAvoidance_le_intensity (normalizeRows P) (normalizeRows_nonneg P hP.1)
    (normalizeRows_rowSum P (fun i => (hr i).ne'))
  have hD := endpoint_original_collisionIntensity_large hm hmn hP hcont
  change 1-originalRowAvoidance P ≤ _ at hU
  linarith

end DittertRybin
