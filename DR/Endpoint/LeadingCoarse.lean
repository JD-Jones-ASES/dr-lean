import DR.Endpoint.LeadingCoarseMinimum
import DR.Endpoint.LeadingEvent

/-! Global quantitative leading-gauge bound for every m>=5 on the full
closed probability simplex. This is an analytic input, not an endpoint
P2 claim; the independent contender and collision estimates are separate. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

theorem endpointLeadingGauge_coarse_lower {m n : ℕ} (hm : 5≤m) (P : Board m n)
    (hP : IsProbability P) :
    Real.sqrt (1-dittertConstant m)+(dittertConstant m/1000)*marginalVariance (rowSum P)≤
      endpointLeadingGauge P := by
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := by omega
    subst n
    have hp := hP.2
    simp [totalMass,rowSum] at hp
  obtain ⟨Q,hmin⟩ := exists_endpointCoarseMinimum (by omega : 0<m) hn
  have hlow := hmin.coarse_value_lower hm hn
  have hcomp := hmin.2 P hP
  rw [endpointCoarsePenalty_variance (by omega : 0<m) (rowSum P) hP.2] at hcomp
  linarith only [hlow,hcomp]

theorem endpointLeadingGauge_coarse_sq_gap {m n : ℕ} (hm : 5≤m) (P : Board m n)
    (hP : IsProbability P) :
    (dittertConstant m/1000)*marginalVariance (rowSum P)≤
      (endpointLeadingGauge P)^2-(1-dittertConstant m) := by
  have h := endpointLeadingGauge_coarse_lower hm P hP
  have ha0 := dittertConstant_pos (by omega : 0<m)
  have ha1 := endpointLeading_alpha_le_five hm
  have hs2 := Real.sq_sqrt (show 0≤1-dittertConstant m by linarith)
  have hsn := Real.sqrt_nonneg (1-dittertConstant m)
  have hs : (1/2:ℝ)≤Real.sqrt (1-dittertConstant m) := by nlinarith only [hs2,hsn,ha1]
  have hv := marginalVariance_nonneg (rowSum P)
  have hz : 0≤(dittertConstant m/1000)*marginalVariance (rowSum P) := by positivity
  have hG := endpointLeadingGauge_nonneg P
  nlinarith only [h,hs2,hz,hs,hG,sq_nonneg (endpointLeadingGauge P-Real.sqrt (1-dittertConstant m))]

theorem endpointLeadingGauge_coarse_sq_lower {m n : ℕ} (hm : 5≤m) (P : Board m n)
    (hP : IsProbability P) : 1-dittertConstant m≤(endpointLeadingGauge P)^2 := by
  have h := endpointLeadingGauge_coarse_sq_gap hm P hP
  have ha := dittertConstant_pos (by omega : 0<m)
  have hz : 0≤(dittertConstant m/1000)*marginalVariance (rowSum P) :=
    mul_nonneg (by positivity : 0≤dittertConstant m/1000) (marginalVariance_nonneg _)
  linarith only [h,hz]

theorem endpointLeading_quadratic_coarse_lower {m n : ℕ} (hm : 5≤m) (hn : 0<n)
    (P : Board m n) (hP : IsProbability P) :
    (1-dittertConstant m+(dittertConstant m/1000)*marginalVariance (rowSum P))/(n:ℝ)≤
      ∑ j,quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hgap := endpointLeadingGauge_coarse_sq_gap hm P hP
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (endpointLeadingColumnCost P) (fun _ : Fin n => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcs
  simp_rw [endpointLeadingColumnCost_sq (by omega : 3≤m) P hP] at hcs
  change (endpointLeadingGauge P)^2≤_ at hcs
  apply (div_le_iff₀ hnR).mpr
  nlinarith only [hgap,hcs]

end DittertRybin
