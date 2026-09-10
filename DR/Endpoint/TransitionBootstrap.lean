import DR.Endpoint.TransitionAvoidance

/-! The original-row avoidance comparison upgrades the actual contender
product deficit and scaled-row variance. The closed simplex is retained;
positive coordinates are conclusions of the product bounds. -/
namespace DittertRybin
open scoped BigOperators

theorem transition_avoidance_ratio_deficit_le (b p u : ℝ) (hb : 0≤b)
    (hq : (1/40001:ℝ)≤1-b) (hpb : p≤b) (hu : 0≤u)
    (hp : b*Real.exp (-u)≤p) : (b-p)/(1-p)≤40001*u := by
  have hp1 : 0<1-p := by linarith
  have he : 1-Real.exp (-u)≤u := by linarith [Real.add_one_le_exp (-u)]
  have hbe := mul_le_mul_of_nonneg_left he hb
  have hbu : b*u≤u := by nlinarith
  have hnum : b-p≤u := by nlinarith only [hp,hbe,hbu]
  apply (div_le_iff₀ hp1).mpr
  have hden : 0≤40001*(1-p)-1 := by linarith
  nlinarith [mul_nonneg hu hden]

theorem endpoint_transition_rowProduct_deficit_lt {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    1-endpointRowProduct P<1/2000 := by
  have hmR : (10^18:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hb := distinctUniformProbability_pos (by omega) hmn
  have hq := endpoint_transition_uniform_failure_lower (by omega) hmn hupper
  have hpB := (endpoint_contender_original_avoidance_bounds (by omega) hmn hP hcont).2.1
  have hp := endpoint_transition_original_avoidance_relative hm hmn hlower hupper hP hcont
  have hr := endpoint_contender_rowProduct_deficit (by omega) hmn hP hcont
  have hu : 0≤7000000000/(m:ℝ) := by positivity
  have hratio := transition_avoidance_ratio_deficit_le (distinctUniformProbability n m)
    (originalRowAvoidance P) (7000000000/(m:ℝ)) hb.le hq hpB hu (by simpa only [neg_div] using hp)
  have hsmall : (40001:ℝ)*(7000000000/(m:ℝ))<1/2000 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hm0).mpr
    linarith
  exact (hr.trans hratio).trans_lt hsmall

/-- The accepted transition row estimate, from the actual full-probability
contender relation on the full closed simplex. -/
theorem endpoint_transition_scaled_row_sq_lt {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hlower : m*(m-1)≤20*n) (hupper : n≤10000*m^2)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/100 := by
  let y : Fin m → ℝ := fun i => (m:ℝ)*rowSum P i
  have hy (i : Fin m) : 0≤y i := mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP.1 i)
  have hs : (∑ i,y i)=m := by
    change (∑ i,(m:ℝ)*rowSum P i)=m
    rw [← Finset.mul_sum,show (∑ i,rowSum P i)=1 from hP.2,mul_one]
  have hdef := endpoint_transition_rowProduct_deficit_lt hm hmn hlower hupper hP hcont
  rw [endpointRowProduct_eq_product] at hdef
  have hp : 1-(1/2000:ℝ)≤∏ i,y i := by linarith
  have h := product_deficit_sq_deviation y hy hs (1/2000) (by norm_num) hp
  exact h.trans_lt (by norm_num)

end DittertRybin
