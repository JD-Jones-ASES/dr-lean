import DR.Endpoint.TransitionRowBounds
import DR.Endpoint.TransitionCollisionScalars
import DR.Endpoint.RowCollisionContenders

/-! The actual original-row collision load and intensity on the accepted
transition range. The intensity estimate uses the proved reciprocal-row
deviation, not the rough minimum row mass. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_transition_collision_bounds {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∀ i,rowCollisionLoad (normalizeRows P) i≤6200000/(m:ℝ)) ∧
    rowCollisionIntensity (normalizeRows P)≤(m:ℝ)^2/(2*(n:ℝ))+3200000001/(m:ℝ) := by
  have hmR : (10^18:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlow : (m:ℝ)*((m:ℝ)-1)≤20*(n:ℝ) := by
    have hc : ((m*(m-1):ℕ):ℝ)≤((20*n:ℕ):ℝ) := by exact_mod_cast hlower
    simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,Nat.cast_ofNat] using hc
  have hsqn : (m:ℝ)^2≤40*(n:ℝ) := by nlinarith
  have hs20 : (m:ℝ)^2/(2*(n:ℝ))≤20 := by
    apply (div_le_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    nlinarith
  have hinv : 1/(n:ℝ)≤40/(m:ℝ)^2 := by
    apply (div_le_div_iff₀ hn0 (sq_pos_of_pos hm0)).mpr
    nlinarith
  have hp4 : (m:ℝ)^2≤(m:ℝ)^4 := by nlinarith [sq_nonneg ((m:ℝ)^2-1)]
  have hinv4 : 1/(m:ℝ)^4≤1/(m:ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hm0) hp4
  have hc (j : Fin n) : colSum P j≤41/(m:ℝ)^2 := by
    have h := endpoint_contender_column_cap_large (by omega) hmn hP hcont j
    have he : 40/(m:ℝ)^2+1/(m:ℝ)^2=41/(m:ℝ)^2 := by ring
    linarith
  obtain ⟨hr,hx,hW⟩ := endpoint_transition_contender_row_bounds (by omega) hmn hupper hP hcont
  have hrmin : 0<1/(150000*(m:ℝ)) := by positivity
  have hrlo (i : Fin m) : 1/(150000*(m:ℝ))≤rowSum P i := by
    apply (div_le_iff₀ (by positivity : 0<150000*(m:ℝ))).mpr
    have hi := (hr i).1
    nlinarith
  have hload (i : Fin m) : rowCollisionLoad (normalizeRows P) i≤6200000/(m:ℝ) := by
    have h := normalizedRow_collisionLoad_le P hP.1 hrmin hrlo hc i
    have he : (41/(m:ℝ)^2)/(1/(150000*(m:ℝ)))=6150000/(m:ℝ) := by field_simp; norm_num
    rw [he] at h
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) hm0.le)
  refine ⟨hload,?_⟩
  have hD := endpoint_original_collisionIntensity_large (by omega) hmn hP hcont
  have hcoef : (1/(n:ℝ)+1/(m:ℝ)^4)*(m:ℝ)^2/2=
      (m:ℝ)^2/(2*(n:ℝ))+1/(2*(m:ℝ)^2) := by field_simp
  rw [hcoef] at hD
  exact hD.trans (transition_intensity_error_le (m:ℝ) ((m:ℝ)^2/(2*(n:ℝ)))
    (endpointRowReciprocalDeviation P) (by linarith) (by positivity) hs20 hW.le)

end DittertRybin
