import DR.Endpoint.LeadingProductGap
import DR.Endpoint.LeadingConstants

/-! Closed-simplex product stability from the proved Newton-Maclaurin
inequality, and its actual leading-norm consequence. Zero row coordinates
are retained in the product theorem. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_row_variance_bounds {m : ℕ} (hm : 0<m) (r : Fin m → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) :
    0≤marginalVariance r ∧ marginalVariance r<1 := by
  have hr1 (i) : r i≤1 := by
    simpa only [hs] using Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hr j)
      (Finset.mem_univ i)
  have hq : (∑ i,(r i)^2)≤1 := by
    rw [← hs]
    exact Finset.sum_le_sum fun i _ => by nlinarith only [hr i,hr1 i]
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hv := marginalVariance_eq_sum_sq hm hs
  refine ⟨marginalVariance_nonneg r,?_⟩
  have hi : 0<1/(m:ℝ) := by positivity
  linarith only [hq,hv,hi]

theorem endpoint_product_le_one_sub_variance {m : ℕ} (hm : 2≤m) (r : Fin m → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) :
    (∏ i,(m:ℝ)*r i)≤1-marginalVariance r := by
  have h0 := normalizedElementarySuccess_nonneg hr 2
  have h1 := normalizedElementarySuccess_le_one hr hs (by decide : 2≤2) hm
  have hp := normalizedElementarySuccess_maclaurin_two hr hm (le_refl m)
  have hpow := pow_le_pow_of_le_one h0 h1 hm
  have hpair : normalizedElementarySuccess r m≤normalizedElementarySuccess r 2 := by
    have hn := normalizedElementarySuccess_nonneg hr m
    nlinarith only [hp,hpow,hn,h0]
  have htop : normalizedElementarySuccess r m=∏ i,(m:ℝ)*r i := by
    simp only [normalizedElementarySuccess,elementaryMean,elementarySymmetric_top,
      Nat.choose_self,Nat.cast_one,div_one,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
  rw [htop,normalizedElementarySuccess_two hm hs] at hpair
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hrat : (1:ℝ)≤(m:ℝ)/((m:ℝ)-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hV := mul_le_mul_of_nonneg_right hrat (marginalVariance_nonneg r)
  linarith only [hpair,hV]

theorem endpointLeadingGauge_coarse_norm_gap {m n : ℕ} (hm : 5≤m)
    (P : Board m n) (hP : IsProbability P)
    (hQ : (endpointLeadingKernel (rowSum P)).PosSemidef) :
    (dittertConstant m/2)*marginalVariance (rowSum P)≤
      endpointLeadingGauge P-Real.sqrt (1-dittertConstant m) := by
  have hm2 : 2≤m := by omega
  have hm0 : 0<m := by omega
  have ha := dittertConstant_pos hm0
  have haU := endpointLeading_alpha_le_five hm
  have hv := (endpoint_row_variance_bounds hm0 (rowSum P) (rowSum_nonneg hP.1) hP.2).1
  have hprod := mul_le_mul_of_nonneg_left
    (endpoint_product_le_one_sub_variance hm2 (rowSum P) (rowSum_nonneg hP.1) hP.2) ha.le
  rw [← endpoint_factorial_product_scaled hm0 (rowSum P)] at hprod
  have hnorm := endpointLeadingGauge_product_lower hm2 P hP hQ
  have hinside : 0≤1-(m.factorial:ℝ)*∏ i,rowSum P i := by
    have hv1 := mul_nonneg ha.le hv
    nlinarith only [hprod,haU,hv1]
  have hG2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  rw [Real.sq_sqrt hinside] at hG2
  have hs2 := Real.sq_sqrt (show 0≤1-dittertConstant m by linarith)
  have hs0 := Real.sqrt_nonneg (1-dittertConstant m)
  have hs1 : Real.sqrt (1-dittertConstant m)≤1 := by nlinarith only [ha,hs2,hs0]
  have hG0 := endpointLeadingGauge_nonneg P
  have hG1 := endpointLeadingGauge_le_one (by omega : 3≤m) P hP
  have hGlo : Real.sqrt (1-dittertConstant m)≤endpointLeadingGauge P := by
    nlinarith only [hG2,hprod,hs2,hs0,hG0,mul_nonneg ha.le hv]
  have hmul := mul_nonneg (sub_nonneg.mpr hGlo)
    (show 0≤2-endpointLeadingGauge P-Real.sqrt (1-dittertConstant m) by linarith only [hG1,hs1])
  nlinarith only [hmul,hG2,hprod,hs2]

end DittertRybin
