import DR.Endpoint.SaturatedRows

/-! Assembly of the saturated-minimum scalar argument. The actual leading
gauge supplies the listed moment and stationarity identities. This module
turns them into the row cap and positive-definite kernel criterion. -/

namespace DittertRybin
open scoped BigOperators

theorem saturated_stationary_reciprocal_bounds {m : ℕ} (hm : 0 < m)
    (r A : Fin m → ℝ) (hr : ∀ i, 0 < r i) {a G D C t : ℝ}
    (ha : 0 < a) (ha1 : a < 1/1000) (hG : 0 < G)
    (hcap : G ≤ Real.sqrt (1-a)+a/1000) (hCS : 1 ≤ G*(G+2*D))
    (hC : C-1 < (1332/275 : ℝ)*a) (hA : ∀ i, 1 ≤ A i ∧ A i ≤ C)
    (ht : t = a*(m : ℝ)^2/(1000*(1+(m : ℝ)^2*marginalVariance r)^2))
    (hstationary : ∀ i, A i = G-((m : ℝ)-2)*D+
      2*t*(r i-(∑ j, (r j)^2))+D/r i) :
    ∀ i j, |1/r i-1/r j| < (1184/121 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : 0 ≤ (m : ℝ)^2*marginalVariance r :=
    mul_nonneg (sq_nonneg _) (marginalVariance_nonneg r)
  have hD := saturated_moment_lower ha ha1 hG hcap hCS
  intro i j
  have hpair := saturated_pair_penalty_cap ha.le hmR hx ht
    (saturated_row_square_cap hm r i) (saturated_row_square_cap hm r j)
  have hid := saturated_stationarity_pair (hr i).ne' (hr j).ne'
    (hstationary i) (hstationary j)
  exact saturated_reciprocal_spread ha hD hpair (hA i) (hA j) hC hid

/-- Strict kernel positivity at the actual stationary scalar data and
the twice-uniform cap needed by the subsequent product gap. -/
theorem saturated_stationary_kernel {m : ℕ} (hm : 96 ≤ m)
    (r A : Fin m → ℝ) (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = 1)
    {a G D C t : ℝ} (ha : 0 < a) (ha1 : a < 1/1000) (hG : 0 < G)
    (hcap : G ≤ Real.sqrt (1-a)+a/1000) (hCS : 1 ≤ G*(G+2*D))
    (hC : C-1 < (1332/275 : ℝ)*a) (hA : ∀ i, 1 ≤ A i ∧ A i ≤ C)
    (ht : t = a*(m : ℝ)^2/(1000*(1+(m : ℝ)^2*marginalVariance r)^2))
    (hstationary : ∀ i, A i = G-((m : ℝ)-2)*D+
      2*t*(r i-(∑ j, (r j)^2))+D/r i)
    (hscale : endpointLeadingScale r ≤ a/((m : ℝ)*((m : ℝ)-1))) :
    (endpointLeadingKernel r).PosDef ∧ (∀ i, r i < 2/(m : ℝ)) := by
  have hmR : (96 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR0 : (0 : ℝ) < m := by linarith
  have hML : (1184/121 : ℝ) < m := by linarith
  have hspread := saturated_stationary_reciprocal_bounds (by omega : 0 < m)
    r A hr ha ha1 hG hcap hCS hC hA ht hstationary
  constructor
  · exact endpointLeadingKernel_posDef r hr hs
      (saturated_rows_psd_criterion hm r hr hs ha1 hscale hspread)
  · intro i
    have hi := (saturated_row_interval r hr hs hML (by norm_num) hspread i).2
    apply hi.trans
    apply (div_lt_div_iff₀ (by linarith : 0 < (m : ℝ)-(1184/121 : ℝ)) hmR0).mpr
    linarith

end DittertRybin
