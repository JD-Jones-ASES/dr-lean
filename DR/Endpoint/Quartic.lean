import DR.Endpoint.LongColumnConcentration
import DR.Endpoint.LeadingCoarse
import DR.Endpoint.LongColumnClosure
import DR.Rectangular.OrderThreeLarge

/-! The full quartic endpoint strip from the global linear gauge modulus.
All contender and retained-kernel conditions are derived for actual boards. -/
namespace DittertRybin
open scoped BigOperators

theorem longColumn_linear_row_bound {M N b v : ℝ}
    (hM : 0<M) (hN : 20000*M^4≤N) (hb : b<M^2/2) (hv : 0≤v)
    (hr : v<503*b/N) : M^2*v<1/16 := by
  have hN0 : 0<N := lt_of_lt_of_le (by positivity) hN
  have h := (lt_div_iff₀ hN0).mp hr
  have hscale := mul_le_mul_of_nonneg_left hN hv
  by_contra hnot
  have hsmall := mul_le_mul_of_nonneg_right (not_lt.mp hnot) (sq_nonneg M)
  nlinarith only [h,hscale,hsmall,hb,sq_pos_of_pos hM]

theorem endpoint_quartic_contender_caps {m n : ℕ} (hm : 16≤m)
    (hn : 20000*m^4≤n) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∑ i, ((m:ℝ)*rowSum P i-1)^2)<1/16 ∧
      (∀ j, colSum P j<25/(n:ℝ)) := by
  have hm0 : 0<m := by omega
  have hmR : (0:ℝ)<m := by exact_mod_cast hm0
  have hnR : (20000:ℝ)*(m:ℝ)^4≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := lt_of_lt_of_le (by positivity) hnR
  have hp : m^2≤m^4 := Nat.pow_le_pow_right hm0 (by decide)
  have hg := endpointLeadingGauge_coarse_sq_lower (by omega : 5≤m) P hP
  have hconc := endpoint_contender_longColumn_concentration hm
    (by omega : 6*m^2≤n) P hP hcont (sub_nonneg.mpr hg)
  have hlin := endpointLeadingGauge_coarse_sq_gap (by omega : 5≤m) P hP
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hratio := longColumn_modulus_lt hn0 (dittertConstant_pos hm0)
    (longColumn_alpha_lt hm) hb.1 hlin hconc.2
  have hrow := longColumn_linear_row_bound hmR hnR hb.2 (marginalVariance_nonneg _) hratio
  rw [endpoint_scaled_variance hm0 (rowSum P)]
  exact ⟨hrow,hconc.1⟩

theorem uniform_maximum_quartic_endpoint_strip {m n : ℕ} (hm : 16≤m)
    (hn : 20000*m^4≤n) : UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  have hm0 : 0<m := by omega
  have hp : m^2≤m^4 := Nat.pow_le_pow_right hm0 (by decide)
  have h := uniform_maximum_endpoint_of_longColumn_caps hm (by omega : 10000*m^2≤n)
    (fun P hP hcont => endpoint_quartic_contender_caps hm hn P hP hcont)
  exact ⟨h,h.transpose⟩

end DittertRybin
