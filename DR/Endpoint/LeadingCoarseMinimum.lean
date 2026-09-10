import DR.Endpoint.LeadingCoarseStationary
import DR.Endpoint.LeadingCoarseProduct

/-! The linear row-variance penalty on the actual closed board simplex.
Stationary data and positive rows are derived at a genuine minimum. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointCoarsePenalty (m : ℕ) (q : ℝ) : ℝ :=
  (dittertConstant m/1000)*(q-1/(m:ℝ))

theorem endpointCoarsePenalty_uniform (m : ℕ) : endpointCoarsePenalty m (1/(m:ℝ))=0 := by
  simp [endpointCoarsePenalty]

theorem endpointCoarsePenalty_variance {m : ℕ} (hm : 0<m) (r : Fin m → ℝ)
    (hs : ∑ i,r i=1) : endpointCoarsePenalty m (∑ i,(r i)^2)=
      (dittertConstant m/1000)*marginalVariance r := by
  rw [marginalVariance_eq_sum_sq hm hs]
  rfl

theorem hasDerivAt_endpointCoarsePenalty (m : ℕ) (q : ℝ) :
    HasDerivAt (endpointCoarsePenalty m) (dittertConstant m/1000) q := by
  have h := ((hasDerivAt_id q).sub_const (1/(m:ℝ))).const_mul (dittertConstant m/1000)
  change HasDerivAt (fun q : ℝ => (dittertConstant m/1000)*(q-1/(m:ℝ))) _ q
  apply h.congr_deriv
  simp only [mul_one]

theorem exists_endpointCoarseMinimum {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    ∃ P : Board m n,IsEndpointGaugeMinimum P (endpointCoarsePenalty m) := by
  exact exists_endpointGaugeMinimum hm hn _ (by unfold endpointCoarsePenalty; fun_prop)

theorem IsEndpointGaugeMinimum.coarse_cap {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointCoarsePenalty m)) :
    endpointLeadingGauge P≤Real.sqrt (1-dittertConstant m)+dittertConstant m/1000 := by
  have h := hmin.le_uniform hm hn
  rw [endpointCoarsePenalty_uniform] at h
  rw [endpointCoarsePenalty_variance (by omega : 0<m) (rowSum P) hmin.1.2] at h
  have hv := (endpoint_row_variance_bounds (by omega : 0<m) (rowSum P)
    (rowSum_nonneg hmin.1.1) hmin.1.2).2
  have ha := dittertConstant_pos (by omega : 0<m)
  nlinarith only [h,hv,ha]

theorem IsEndpointGaugeMinimum.coarse_kernel {m n : ℕ} (hm : 5≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointCoarsePenalty m)) :
    (endpointLeadingKernel (rowSum P)).PosDef := by
  have hm0 : 0<m := by omega
  have hm3 : 3≤m := by omega
  have ha := dittertConstant_pos hm0
  have haU := endpointLeading_alpha_le_five hm
  have hcap := hmin.coarse_cap (by omega) hn
  have hG1 := hcap.trans_lt (endpoint_coarse_sqrt_cap ha haU).2
  have hr := endpointLeading_rows_pos_of_lt_one P hmin.1 hG1
  have hX := normalizeRows_nonneg P hmin.1.1
  have hXS := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hrec := endpointRowBoard_normalizeRows P (fun i => (hr i).ne')
  have hG := endpointLeadingGauge_pos hm3 (rowSum P) (normalizeRows P)
    (fun i => (hr i).le) hmin.1.2 hX hXS
  have hCS := endpointLeading_weighted_cauchy hm3 (rowSum P) (normalizeRows P)
    (fun i => (hr i).le) hmin.1.2 hX hXS
  rw [hrec] at hG hCS
  have hstationary := hmin.stationarity hm3 hr (dittertConstant m/1000)
    (hasDerivAt_endpointCoarsePenalty m _)
  have hA := endpointLeadingRowDerivative_bounds hm3 (rowSum P) (normalizeRows P)
    hr hmin.1.2 hX hXS
  exact endpoint_coarse_stationary_kernel hm (rowSum P)
    (endpointLeadingRowDerivative (rowSum P) (normalizeRows P)) hr hmin.1.2
    ha haU hG hcap hCS (endpointLeadingRatioCap_sub_one_lt hm) hA hstationary
    (endpointLeadingScale_le (by omega) (rowSum P) (fun i => (hr i).le) hmin.1.2)

theorem IsEndpointGaugeMinimum.coarse_value_lower {m n : ℕ} (hm : 5≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointCoarsePenalty m)) :
    Real.sqrt (1-dittertConstant m)≤
      endpointLeadingGauge P-endpointCoarsePenalty m (∑ i,(rowSum P i)^2) := by
  have hgap := endpointLeadingGauge_coarse_norm_gap hm P hmin.1 (hmin.coarse_kernel hm hn).posSemidef
  rw [endpointCoarsePenalty_variance (by omega : 0<m) (rowSum P) hmin.1.2]
  have ha := (dittertConstant_pos (by omega : 0<m)).le
  have hv := marginalVariance_nonneg (rowSum P)
  nlinarith only [hgap,mul_nonneg ha hv]

end DittertRybin
