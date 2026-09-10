import DR.Endpoint.LeadingProductGap
import DR.Endpoint.LeadingConstants
import DR.Endpoint.SaturatedStationary

/-! The saturated penalty and its actual minimum on the full probability
simplex. The rational penalty is continuous on the attained row-square
domain; no assertion of global continuity across its irrelevant pole is used. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointSaturatedPenalty (m : ℕ) (q : ℝ) : ℝ :=
  (dittertConstant m/1000)*(((m:ℝ)^2*(q-1/(m:ℝ)))/(1+(m:ℝ)^2*(q-1/(m:ℝ))))

theorem endpointSaturatedPenalty_uniform (m : ℕ) :
    endpointSaturatedPenalty m (1/(m:ℝ))=0 := by
  simp [endpointSaturatedPenalty]

theorem endpointSaturatedPenalty_variance {m : ℕ} (hm : 0<m) (r : Fin m → ℝ)
    (hs : ∑ i,r i=1) :
    endpointSaturatedPenalty m (∑ i,(r i)^2)=
      (dittertConstant m/1000)*(((m:ℝ)^2*marginalVariance r)/(1+(m:ℝ)^2*marginalVariance r)) := by
  rw [marginalVariance_eq_sum_sq hm hs]
  rfl

theorem endpointSaturatedPenalty_bounds {m : ℕ} (hm : 0<m) (r : Fin m → ℝ)
    (hs : ∑ i,r i=1) :
    0≤endpointSaturatedPenalty m (∑ i,(r i)^2) ∧
    endpointSaturatedPenalty m (∑ i,(r i)^2)≤dittertConstant m/1000 := by
  rw [endpointSaturatedPenalty_variance hm r hs]
  have hx : 0≤(m:ℝ)^2*marginalVariance r :=
    mul_nonneg (sq_nonneg _) (marginalVariance_nonneg r)
  have hd : 0<1+(m:ℝ)^2*marginalVariance r := by positivity
  have ha : 0≤dittertConstant m := (dittertConstant_pos hm).le
  constructor
  · positivity
  · have h := (div_le_one hd).mpr (show (m:ℝ)^2*marginalVariance r≤1+(m:ℝ)^2*marginalVariance r by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤dittertConstant m/1000)

theorem hasDerivAt_endpointSaturatedPenalty {m : ℕ} {q : ℝ}
    (hd : 1+(m:ℝ)^2*(q-1/(m:ℝ))≠0) :
    HasDerivAt (endpointSaturatedPenalty m)
      (dittertConstant m*(m:ℝ)^2/(1000*(1+(m:ℝ)^2*(q-1/(m:ℝ)))^2)) q := by
  have hx := ((hasDerivAt_id q).sub_const (1/(m:ℝ))).const_mul ((m:ℝ)^2)
  have h := (hx.div (hx.const_add 1) hd).const_mul (dittertConstant m/1000)
  change HasDerivAt (fun q : ℝ =>
    (dittertConstant m/1000)*(((m:ℝ)^2*(q-1/(m:ℝ)))/(1+(m:ℝ)^2*(q-1/(m:ℝ))))) _ q
  apply h.congr_deriv
  simp only [id_eq,mul_one]
  field_simp
  ring

/-- The denominator is positive throughout the actual closed board simplex. -/
theorem endpointSaturatedPenalty_continuousOn {m n : ℕ} (hm : 0<m) :
    ContinuousOn (fun P : Board m n =>
      endpointLeadingGauge P-endpointSaturatedPenalty m (∑ i,(rowSum P i)^2))
      {P : Board m n | IsProbability P} := by
  intro P hP
  apply (continuous_endpointLeadingGauge m n).continuousWithinAt.sub
  have hv := marginalVariance_nonneg (rowSum P)
  rw [marginalVariance_eq_sum_sq hm hP.2] at hv
  have hd : 1+(m:ℝ)^2*((∑ i,(rowSum P i)^2)-1/(m:ℝ))≠0 :=
    ne_of_gt (by positivity)
  have hc : Continuous (fun P : Board m n => ∑ i,(rowSum P i)^2) := by
    unfold rowSum
    fun_prop
  exact (hasDerivAt_endpointSaturatedPenalty hd).continuousAt.comp_continuousWithinAt
    (f:=fun P : Board m n => ∑ i,(rowSum P i)^2) hc.continuousWithinAt

theorem exists_endpointSaturatedMinimum {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    ∃ P : Board m n, IsEndpointGaugeMinimum P (endpointSaturatedPenalty m) := by
  obtain ⟨P,hP,hmin⟩ := (isCompact_probabilitySimplex m n).exists_isMinOn
    ⟨uniformBoard m n,uniformBoard_isProbability hm hn⟩
    (endpointSaturatedPenalty_continuousOn hm)
  exact ⟨P,hP,fun Q hQ => hmin hQ⟩

theorem IsEndpointGaugeMinimum.saturated_cap {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointSaturatedPenalty m)) :
    endpointLeadingGauge P≤Real.sqrt (1-dittertConstant m)+dittertConstant m/1000 := by
  have h := hmin.le_uniform hm hn
  rw [endpointSaturatedPenalty_uniform] at h
  have hb := (endpointSaturatedPenalty_bounds (by omega : 0<m) (rowSum P) hmin.1.2).2
  linarith

/-- Kernel positivity and the twice-uniform cap are derived at a true full-simplex minimum. -/
theorem IsEndpointGaugeMinimum.saturated_kernel {m n : ℕ} (hm : 96≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointSaturatedPenalty m)) :
    (endpointLeadingKernel (rowSum P)).PosDef ∧
      (∀ i,0<rowSum P i ∧ rowSum P i<2/(m:ℝ)) := by
  have hm0 : 0<m := by omega
  have hm3 : 3≤m := by omega
  have ha := dittertConstant_pos hm0
  have ha1 := endpointLeading_alpha_lt_thousandth (by omega : 10≤m)
  have hcap := hmin.saturated_cap (by omega) hn
  have hG1 := hcap.trans_lt (saturated_sqrt_cap ha ha1).2
  have hr := endpointLeading_rows_pos_of_lt_one P hmin.1 hG1
  have hX := normalizeRows_nonneg P hmin.1.1
  have hXS := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hrec := endpointRowBoard_normalizeRows P (fun i => (hr i).ne')
  have hG := endpointLeadingGauge_pos hm3 (rowSum P) (normalizeRows P)
    (fun i => (hr i).le) hmin.1.2 hX hXS
  have hCS := endpointLeading_weighted_cauchy hm3 (rowSum P) (normalizeRows P)
    (fun i => (hr i).le) hmin.1.2 hX hXS
  rw [hrec] at hG hCS
  let tau := dittertConstant m*(m:ℝ)^2/(1000*(1+(m:ℝ)^2*marginalVariance (rowSum P))^2)
  have hpsi : HasDerivAt (endpointSaturatedPenalty m) tau (∑ i,(rowSum P i)^2) := by
    have hv := marginalVariance_nonneg (rowSum P)
    have hd : 1+(m:ℝ)^2*marginalVariance (rowSum P)≠0 := ne_of_gt (by positivity)
    rw [marginalVariance_eq_sum_sq hm0 hmin.1.2] at hd
    have h := hasDerivAt_endpointSaturatedPenalty hd
    simpa only [tau,marginalVariance_eq_sum_sq hm0 hmin.1.2] using h
  have hstationary := hmin.stationarity hm3 hr tau hpsi
  have hA := endpointLeadingRowDerivative_bounds hm3 (rowSum P) (normalizeRows P)
    hr hmin.1.2 hX hXS
  have hkernel := saturated_stationary_kernel hm (rowSum P)
    (endpointLeadingRowDerivative (rowSum P) (normalizeRows P)) hr hmin.1.2
    ha ha1 hG hcap hCS (endpointLeadingRatioCap_sub_one_lt (by omega)) hA rfl hstationary
    (endpointLeadingScale_le (by omega) (rowSum P) (fun i => (hr i).le) hmin.1.2)
  exact ⟨hkernel.1,fun i => ⟨hr i,hkernel.2 i⟩⟩

end DittertRybin
