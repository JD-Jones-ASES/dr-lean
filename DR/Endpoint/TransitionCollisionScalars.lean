import DR.Endpoint.RowCollisionLogBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact real arithmetic in the refined transition collision comparison.
The intensity bound keeps its reciprocal-row normalization, and the log
bound keeps the local-lemma denominator. -/
namespace DittertRybin

theorem transition_intensity_error_le (M s W : ℝ) (hM : 160000000≤M)
    (hs0 : 0≤s) (hs : s≤20) (hW : W≤160000000) :
    (s+1/(2*M^2))*(1+W/M)≤s+3200000001/M := by
  have hM0 : 0<M := by linarith
  have hfirst : 0≤s+1/(2*M^2) := by positivity
  calc
    _≤(s+1/(2*M^2))*(1+160000000/M) := by
      apply mul_le_mul_of_nonneg_left _ hfirst
      exact add_le_add le_rfl (div_le_div_of_nonneg_right hW hM0.le)
    _≤_ := by
      field_simp
      have hsq : 0≤M^2 := sq_nonneg M
      have hsM := mul_nonneg (sub_nonneg.mpr hs) hsq
      nlinarith [sq_nonneg (M-1)]

theorem transition_log_denominator_bound (M s D : ℝ) (hM : (10^18:ℝ)≤M)
    (hs : s≤20) (hD : D≤s+3200000001/M) :
    D/(1-5*(6200000/M))≤s+6000000000/M := by
  have hM0 : 0<M := by linarith
  have hsmall : (6200000:ℝ)/M≤1/8 := by
    apply (div_le_iff₀ hM0).mpr
    linarith
  have hden : 0<1-5*(6200000/M) := by linarith
  apply (div_le_iff₀ hden).mpr
  apply hD.trans
  field_simp
  have hsM := mul_nonneg (sub_nonneg.mpr hs) hM0.le
  nlinarith

end DittertRybin
