import DR.Endpoint.LongColumnAbsorption
import DR.Endpoint.LongColumnParameters
import DR.Endpoint.LeadingContenderComparison

/-! Actual contender concentration from the retained-uniform probability
comparison and a nonnegative global leading-gauge gap. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_contender_longColumn_concentration {m n : ℕ} (hm : 16≤m)
    (hn : 6*m^2≤n) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (hg : 0≤(endpointLeadingGauge P)^2-(1-dittertConstant m)) :
    (∀ j, colSum P j<25/(n:ℝ)) ∧
      (endpointLeadingGauge P)^2-(1-dittertConstant m)≤
        dittertConstant m*(endpointColumnLossFactor m/2+
          1875*dittertConstant m*endpointColumnLossFactor m)/(n:ℝ) := by
  have hm0 : 0<m := by omega
  have hmn : m≤n := by
    have h : m≤m^2 := Nat.le_self_pow (by decide) m
    omega
  have hn0 : 0<n := lt_of_lt_of_le hm0 hmn
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (colSum P)
    ⟨⟨0,hn0⟩,Finset.mem_univ _⟩
  have hmax' (k) : colSum P k≤colSum P j := hmax k (Finset.mem_univ k)
  have hcomp := endpoint_contender_leading_comparison (by omega : 3≤m) hmn P hP hcont
    (colSum P j) hmax'
  change (endpointLeadingGauge P)^2-(1-dittertConstant m)+
    (n:ℝ)*centeredVariance (endpointLeadingColumnCost P)≤
    (n:ℝ)*endpointColumnLossFactor m*colSum P j*marginalVariance (colSum P)+
      dittertConstant m*endpointColumnLossFactor m/(2*(n:ℝ)) at hcomp
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hr := endpointLeadingRho_bounds (by omega : 5≤m)
  have hp := longColumn_scalar_parameters hm
  have hW := centeredVariance_nonneg (endpointLeadingColumnCost P)
  have habs := longColumn_absorb_variance hnR hb.1.le (colSum_nonneg hP.1 j) hW
    (longColumn_contender_initial_loss hm hn hP hcont j)
    (endpointLeading_variance_conversion (by omega : 5≤m) hn0 P hP) hcomp
  have hcap := longColumn_cap_twenty_five hnR (colSum_nonneg hP.1 j) hg hp.1 hp.2 habs
    (endpointLeading_column_sq_le (by omega : 5≤m) hn0 P hP j)
  exact ⟨fun k => (hmax' k).trans_lt hcap,
    longColumn_gap_after_cap hnR (dittertConstant_pos hm0).le hb.1.le hr.1 hr.2.2 hW hcap habs⟩

/-- The exact small-factorial guard turns either gauge modulus into the
same scalar503 bound. -/
theorem longColumn_modulus_lt {N a b z g : ℝ} (hN : 0<N) (ha : 0<a)
    (haU : a<1/625000) (hb : 0<b) (hz : (a/1000)*z≤g)
    (hg : g≤a*(b/2+1875*a*b)/N) : z<503*b/N := by
  have h := mul_le_mul_of_nonneg_right (hz.trans hg) hN.le
  have hid : (a*(b/2+1875*a*b)/N)*N=a*(b/2+1875*a*b) := by field_simp
  rw [hid] at h
  have hf : a*(z*N/1000)≤a*(b/2+1875*a*b) := by nlinarith only [h]
  have hcancel := (mul_le_mul_iff_right₀ ha).mp hf
  have hsmall := mul_lt_mul_of_pos_right haU hb
  apply (lt_div_iff₀ hN).mpr
  nlinarith only [hcancel,hsmall]

end DittertRybin
