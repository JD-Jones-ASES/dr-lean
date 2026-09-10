import DR.Endpoint.LongColumnConcentration
import DR.Endpoint.LeadingSaturated
import DR.Endpoint.LongColumnClosure
import DR.Rectangular.OrderThreeLarge

/-! The full quadratic endpoint strip, on the closed probability simplex.
Saturated gauge stability and the retained-uniform comparison give actual
contender caps; collision-cluster positivity then gives strict averaging. -/
namespace DittertRybin
open scoped BigOperators

theorem longColumn_saturated_row_bound {M N b x : ℝ}
    (hM : 0<M) (hN : 10000*M^2≤N) (hb : b<M^2/2) (hx : 0≤x)
    (hr : x/(1+x)<503*b/N) : x<1/16 := by
  have hN0 : 0<N := lt_of_lt_of_le (by positivity) hN
  have hsmall : 503*b/N<1/32 := by
    apply (div_lt_iff₀ hN0).mpr
    nlinarith only [hN,hb,sq_pos_of_pos hM]
  have h := (div_lt_iff₀ (show 0<1+x by positivity)).mp (hr.trans hsmall)
  nlinarith only [h]

theorem endpoint_quadratic_contender_caps {m n : ℕ} (hm : 96≤m)
    (hn : 10000*m^2≤n) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∑ i, ((m:ℝ)*rowSum P i-1)^2)<1/16 ∧
      (∀ j, colSum P j<25/(n:ℝ)) := by
  have hm0 : 0<m := by omega
  have hmR : (0:ℝ)<m := by exact_mod_cast hm0
  have hnR : (10000:ℝ)*(m:ℝ)^2≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := lt_of_lt_of_le (by positivity) hnR
  have hg := endpointLeadingGauge_sq_lower hm P hP
  have hconc := endpoint_contender_longColumn_concentration (by omega : 16≤m)
    (by omega : 6*m^2≤n) P hP hcont (sub_nonneg.mpr hg)
  have hsat := endpointLeadingGauge_saturated_sq_gap hm P hP
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hratio := longColumn_modulus_lt hn0 (dittertConstant_pos hm0)
    (longColumn_alpha_lt (by omega : 16≤m)) hb.1 hsat hconc.2
  have hx : 0≤(m:ℝ)^2*marginalVariance (rowSum P) :=
    mul_nonneg (sq_nonneg _) (marginalVariance_nonneg _)
  have hrow := longColumn_saturated_row_bound hmR hnR hb.2 hx hratio
  rw [endpoint_scaled_variance hm0 (rowSum P)]
  exact ⟨hrow,hconc.1⟩

/-- Every actual m-by-N probability matrix is bounded sharply by uniformity,
with iff equality, throughout the quadratic strip and its transpose. -/
theorem uniform_maximum_quadratic_endpoint_strip {m n : ℕ} (hm : 96≤m)
    (hn : 10000*m^2≤n) : UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  have h := uniform_maximum_endpoint_of_longColumn_caps (by omega : 16≤m) hn
    (fun P hP hcont => endpoint_quadratic_contender_caps hm hn P hP hcont)
  exact ⟨h,h.transpose⟩

end DittertRybin
