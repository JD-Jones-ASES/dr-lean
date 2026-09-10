import DR.Endpoint.BoundaryPermanentRatio

/-! The exact Bernoulli and square-completion contradiction in the
boundary-permanent scaling method. The deficit-zero case is retained.
All dimension estimates and all matrix inequalities remain separate inputs. -/

namespace DittertRybin

theorem endpoint_boundary_scaling_contradiction {m : ℕ}
    {b kappa L delta t : ℝ} (hb : 0 < b) (hk : 0 < kappa)
    (hL : 0 ≤ L) (hd : 0 ≤ delta) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (htsq : t^2 = L*delta)
    (hgap : (m : ℝ)^2*b*L/4 < (kappa-1)/kappa^2)
    (hboundary : (1-t)^m*b*kappa ≤ b-delta) : False := by
  have hgap' : (m : ℝ)^2*b*L*kappa^2 < 4*(kappa-1) := by
    have h := (lt_div_iff₀ (sq_pos_of_pos hk)).mp hgap
    nlinarith only [h]
  have hkn : 0 < kappa-1 := by
    have hnonneg : 0 ≤ (m : ℝ)^2*b*L*kappa^2 := by positivity
    linarith
  have hber : 1-(m : ℝ)*t ≤ (1-t)^m := by
    simpa only [mul_neg, ← sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -t) (by linarith : -2 ≤ -t) m)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hber hb.le) hk.le
  have hlin : delta+b*(kappa-1) ≤ (m : ℝ)*b*kappa*t := by
    nlinarith only [hmul, hboundary]
  have hdpos : 0 < delta := by
    by_contra hn
    have hdz : delta = 0 := le_antisymm (le_of_not_gt hn) hd
    have htz : t = 0 := by rw [hdz, mul_zero] at htsq; nlinarith only [htsq]
    rw [hdz, htz] at hlin
    have hpos := mul_pos hb hkn
    nlinarith only [hlin, hpos]
  have hleft : 0 ≤ delta+b*(kappa-1) := by positivity
  have hright : 0 ≤ (m : ℝ)*b*kappa*t := by positivity
  have hsq := pow_le_pow_left₀ hleft hlin 2
  have hrhs : ((m : ℝ)*b*kappa*t)^2 = (m : ℝ)^2*b^2*kappa^2*L*delta := by
    calc
      _ = (m : ℝ)^2*b^2*kappa^2*t^2 := by ring
      _ = _ := by rw [htsq]; ring
  rw [hrhs] at hsq
  have hfinal : 4*b*(kappa-1) ≤ (m : ℝ)^2*b^2*kappa^2*L := by
    apply (mul_le_mul_iff_right₀ hdpos).mp
    nlinarith only [hsq, sq_nonneg (delta-b*(kappa-1))]
  have hstrict := mul_lt_mul_of_pos_left hgap' hb
  nlinarith only [hfinal, hstrict]

end DittertRybin
