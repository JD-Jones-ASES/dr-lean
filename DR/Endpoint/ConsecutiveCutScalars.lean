import DR.Endpoint.BoundaryScalingScalars

/-! A cut-dependent permanent floor and a one-sided quadratic dilation
estimate suffice for the same exact square-completion contradiction. -/

namespace DittertRybin

theorem endpoint_sized_scaling_contradiction {m : ℕ}
    {b beta L delta t : ℝ} (hb : 0 < b) (hL : 0 ≤ L)
    (hd : 0 ≤ delta) (_ht : 0 ≤ t) (ht1 : t ≤ 1)
    (htsq : t^2 ≤ L*delta)
    (hgap : 0 < beta-b-(m : ℝ)^2*L*beta^2/4)
    (hboundary : (1-t)^m*beta ≤ b-delta) : False := by
  have hgb : 0 < beta-b := by
    have hnonneg : 0 ≤ (m : ℝ)^2*L*beta^2/4 := by positivity
    linarith
  have hbeta : 0 < beta := by linarith
  have hber : 1-(m : ℝ)*t ≤ (1-t)^m := by
    simpa only [mul_neg, ← sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -t) (by linarith : -2 ≤ -t) m)
  have hlin : delta+(beta-b) ≤ (m : ℝ)*beta*t := by
    have h := mul_le_mul_of_nonneg_right hber hbeta.le
    nlinarith only [h, hboundary]
  have hdpos : 0 < delta := by
    by_contra hn
    have hdz : delta = 0 := le_antisymm (le_of_not_gt hn) hd
    have htz : t = 0 := by rw [hdz, mul_zero] at htsq; nlinarith only [htsq]
    rw [hdz, htz] at hlin
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ delta+(beta-b)) hlin 2
  have hscale := mul_le_mul_of_nonneg_left htsq
    (by positivity : 0 ≤ (m : ℝ)^2*beta^2)
  have hfinal : 4*(beta-b) ≤ (m : ℝ)^2*L*beta^2 := by
    apply (mul_le_mul_iff_right₀ hdpos).mp
    nlinarith only [hsq, hscale, sq_nonneg (delta-(beta-b))]
  linarith

end DittertRybin
