import DR.Endpoint.RepeatedCellConcentration
import DR.Endpoint.LeadingCoarse
import DR.Endpoint.LongColumnConcentration
import Mathlib.Tactic.IntervalCases

/-! Actual contender concentration in the bounded row range5..15 at the
accepted quadratic cutoff10^11 m². The first cap uses a literal repeated
cell event; no small-row version of the desired P2 theorem is assumed. -/
namespace DittertRybin
open scoped BigOperators

theorem smallRow_scalar_parameters {m : ℕ} (hm : 5≤m) (hmU : m≤15) :
    dittertConstant m*endpointColumnLossFactor m<1 ∧
      endpointColumnLossFactor m*(endpointLeadingRho m)^2<1 := by
  have hfinite : dittertConstant m*endpointColumnLossFactor m<1 ∧
      25*endpointColumnLossFactor m*(dittertConstant m)^2<1 := by
    interval_cases m <;> norm_num [dittertConstant,endpointColumnLossFactor,Nat.factorial]
  have hr := endpointLeadingRho_bounds hm
  have hr2 := pow_le_pow_left₀ hr.1 hr.2.2 2
  have hb := (endpointColumnLossFactor_bounds (by omega : 3≤m)).1.le
  exact ⟨hfinite.1,by nlinarith only [hfinite.2,mul_le_mul_of_nonneg_left hr2 hb]⟩

theorem smallRow_initial_loss {m n : ℕ} (hm : 5≤m) (hmU : m≤15)
    (hn : 100000000000*m^2≤n) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    endpointColumnLossFactor m*colSum P j<1/6 := by
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hmUR : (m:ℝ)≤15 := by exact_mod_cast hmU
  have hnR : (100000000000:ℝ)*(m:ℝ)^2≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by nlinarith
  have hmn : m≤n := by have h := Nat.le_self_pow (by decide : 2≠0) m; omega
  have hcol := endpoint_contender_repeatedCell_column_sq (by omega : 2≤m) hmn P hP hcont j
  rw [endpoint_choose_two_real (by omega : 2≤m)] at hcol
  have hmul := (le_div_iff₀ hn0).mp hcol
  have hsq : (colSum P j)^2<1/1000000 := by
    by_contra h
    have hc := not_lt.mp h
    have hN := mul_le_mul_of_nonneg_right hnR (sq_nonneg (colSum P j))
    nlinarith only [hmR,hmUR,hmul,hc,hN,sq_nonneg ((m:ℝ)-5),sq_nonneg ((m:ℝ)-15)]
  have hc0 := colSum_nonneg hP.1 j
  have hc : colSum P j<1/1000 := by nlinarith only [hc0,hsq]
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hbU : endpointColumnLossFactor m<225/2 := by nlinarith only [hb.2,hmR,hmUR]
  have hmultiply := mul_lt_mul_of_pos_left hc hb.1
  nlinarith only [hmultiply,hbU]

theorem smallRow_modulus_le {N a b z g : ℝ} (hN : 0<N) (ha : 0<a)
    (haU : a≤1/25) (hb : 0≤b) (hz : (a/1000)*z≤g)
    (hg : g≤a*(b/2+1875*a*b)/N) : z≤75500*b/N := by
  have h := mul_le_mul_of_nonneg_right (hz.trans hg) hN.le
  have hid : (a*(b/2+1875*a*b)/N)*N=a*(b/2+1875*a*b) := by field_simp
  rw [hid] at h
  have hf : a*(z*N/1000)≤a*(b/2+1875*a*b) := by nlinarith only [h]
  have hcancel := (mul_le_mul_iff_right₀ ha).mp hf
  have hsmall := mul_le_mul_of_nonneg_right haU hb
  apply (le_div_iff₀ hN).mpr
  nlinarith only [hcancel,hsmall]

theorem endpoint_smallRow_contender_caps {m n : ℕ} (hm : 5≤m) (hmU : m≤15)
    (hn : 100000000000*m^2≤n) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/16 ∧ (∀ j,colSum P j<25/(n:ℝ)) := by
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hmUR : (m:ℝ)≤15 := by exact_mod_cast hmU
  have hnR : (100000000000:ℝ)*(m:ℝ)^2≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by nlinarith
  have hmn : m≤n := by have h := Nat.le_self_pow (by decide : 2≠0) m; omega
  have hnN : 0<n := by omega
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (colSum P)
    ⟨⟨0,hnN⟩,Finset.mem_univ _⟩
  have hmax' (k) : colSum P k≤colSum P j := hmax k (Finset.mem_univ k)
  have hcomp := endpoint_contender_leading_comparison (by omega : 3≤m) hmn P hP hcont
    (colSum P j) hmax'
  change (endpointLeadingGauge P)^2-(1-dittertConstant m)+
    (n:ℝ)*centeredVariance (endpointLeadingColumnCost P)≤
    (n:ℝ)*endpointColumnLossFactor m*colSum P j*marginalVariance (colSum P)+
      dittertConstant m*endpointColumnLossFactor m/(2*(n:ℝ)) at hcomp
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hr := endpointLeadingRho_bounds hm
  have hp := smallRow_scalar_parameters hm hmU
  have hW := centeredVariance_nonneg (endpointLeadingColumnCost P)
  have hg := sub_nonneg.mpr (endpointLeadingGauge_coarse_sq_lower hm P hP)
  have habs := longColumn_absorb_variance hn0 hb.1.le (colSum_nonneg hP.1 j) hW
    (smallRow_initial_loss hm hmU hn P hP hcont j)
    (endpointLeading_variance_conversion hm hnN P hP) hcomp
  have hcap := longColumn_cap_twenty_five hn0 (colSum_nonneg hP.1 j) hg hp.1 hp.2 habs
    (endpointLeading_column_sq_le hm hnN P hP j)
  have ha := dittertConstant_pos (by omega : 0<m)
  have hgap := longColumn_gap_after_cap hn0 ha.le hb.1.le hr.1 hr.2.2 hW hcap habs
  have hnu := smallRow_modulus_le hn0 ha
    (show dittertConstant m≤1/25 from (endpointLeading_alpha_le_five hm).trans (by norm_num))
    hb.1.le (endpointLeadingGauge_coarse_sq_gap hm P hP) hgap
  have hbU : endpointColumnLossFactor m<225/2 := by nlinarith only [hb.2,hmR,hmUR]
  have hnuN := (le_div_iff₀ hn0).mp hnu
  have hv := marginalVariance_nonneg (rowSum P)
  have hscale := mul_le_mul_of_nonneg_right hnR hv
  have hrow : (m:ℝ)^2*marginalVariance (rowSum P)<1/16 := by
    nlinarith only [hnuN,hscale,hbU]
  rw [endpoint_scaled_variance (by omega : 0<m) (rowSum P)]
  exact ⟨hrow,fun k => (hmax' k).trans_lt hcap⟩

end DittertRybin
