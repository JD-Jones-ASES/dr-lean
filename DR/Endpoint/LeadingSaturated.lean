import DR.Endpoint.LeadingSaturatedMinimum

/-! Global saturated leading-gauge stability for every probability board with
at least96 rows. This closes the actual compact-minimum argument; it does
not yet supply the separate contender comparison for endpoint P2. -/
namespace DittertRybin
open scoped BigOperators

theorem IsEndpointGaugeMinimum.saturated_value_lower {m n : ℕ} (hm : 96≤m) (hn : 0<n)
    {P : Board m n} (hmin : IsEndpointGaugeMinimum P (endpointSaturatedPenalty m)) :
    Real.sqrt (1-dittertConstant m)≤
      endpointLeadingGauge P-endpointSaturatedPenalty m (∑ i,(rowSum P i)^2) := by
  obtain ⟨hQ,hr⟩ := hmin.saturated_kernel hm hn
  have hgap := endpointLeadingGauge_saturated_norm_gap (by omega : 2≤m) P hmin.1
    (fun i => (hr i).1) (fun i => (hr i).2.le) hQ.posSemidef
  let x := (m:ℝ)^2*marginalVariance (rowSum P)
  have hx : 0≤x := mul_nonneg (sq_nonneg _) (marginalVariance_nonneg _)
  have ha : 0≤dittertConstant m := (dittertConstant_pos (by omega : 0<m)).le
  have hsmall : endpointSaturatedPenalty m (∑ i,(rowSum P i)^2)≤
      dittertConstant m*x/(16*(1+x)) := by
    rw [endpointSaturatedPenalty_variance (by omega : 0<m) (rowSum P) hmin.1.2]
    change (dittertConstant m/1000)*(x/(1+x))≤dittertConstant m*x/(16*(1+x))
    have he : (dittertConstant m/1000)*(x/(1+x))=dittertConstant m*x/(1000*(1+x)) := by
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_left (mul_nonneg ha hx) (by positivity)
    linarith
  change dittertConstant m*x/(16*(1+x))≤_ at hgap
  linarith

/-- The saturated stability estimate holds on the entire closed probability simplex. -/
theorem endpointLeadingGauge_saturated_lower {m n : ℕ} (hm : 96≤m) (P : Board m n)
    (hP : IsProbability P) :
    Real.sqrt (1-dittertConstant m)+
      (dittertConstant m/1000)*(((m:ℝ)^2*marginalVariance (rowSum P))/
        (1+(m:ℝ)^2*marginalVariance (rowSum P)))≤endpointLeadingGauge P := by
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := by omega
    subst n
    have hp := hP.2
    simp [totalMass,rowSum] at hp
  obtain ⟨Q,hmin⟩ := exists_endpointSaturatedMinimum (by omega : 0<m) hn
  have hlow := hmin.saturated_value_lower hm hn
  have hcomp := hmin.2 P hP
  rw [endpointSaturatedPenalty_variance (by omega : 0<m) (rowSum P) hP.2] at hcomp
  linarith

theorem endpointLeadingGauge_saturated_sq_gap {m n : ℕ} (hm : 96≤m) (P : Board m n)
    (hP : IsProbability P) :
    (dittertConstant m/1000)*(((m:ℝ)^2*marginalVariance (rowSum P))/
      (1+(m:ℝ)^2*marginalVariance (rowSum P)))≤
        (endpointLeadingGauge P)^2-(1-dittertConstant m) := by
  have h := endpointLeadingGauge_saturated_lower hm P hP
  have ha0 := dittertConstant_pos (by omega : 0<m)
  have ha1 := endpointLeading_alpha_lt_thousandth (by omega : 10≤m)
  have hs2 := Real.sq_sqrt (show 0≤1-dittertConstant m by linarith)
  have hsn := Real.sqrt_nonneg (1-dittertConstant m)
  have hs : (1/2:ℝ)≤Real.sqrt (1-dittertConstant m) := by nlinarith
  have hv := marginalVariance_nonneg (rowSum P)
  have hz : 0≤(dittertConstant m/1000)*(((m:ℝ)^2*marginalVariance (rowSum P))/
      (1+(m:ℝ)^2*marginalVariance (rowSum P))) := by positivity
  have hG := endpointLeadingGauge_nonneg P
  nlinarith only [h,hs2,hz,hs,hG,sq_nonneg (endpointLeadingGauge P-Real.sqrt (1-dittertConstant m))]

theorem endpointLeadingGauge_sq_lower {m n : ℕ} (hm : 96≤m) (P : Board m n)
    (hP : IsProbability P) : 1-dittertConstant m≤(endpointLeadingGauge P)^2 := by
  have h := endpointLeadingGauge_saturated_sq_gap hm P hP
  have hv := marginalVariance_nonneg (rowSum P)
  have ha := dittertConstant_pos (by omega : 0<m)
  have hz : 0≤(dittertConstant m/1000)*(((m:ℝ)^2*marginalVariance (rowSum P))/
      (1+(m:ℝ)^2*marginalVariance (rowSum P))) := by positivity
  linarith

end DittertRybin
