import DR.Endpoint.TransitionProductBounds
import DR.Endpoint.UniformAvoidanceBound
import DR.Endpoint.RowCollisionBounds

/-! Initial row bounds for actual endpoint contenders in the transition
range n≤10000m². This is the coarse input of the accepted all-aspect proof;
it is not the refined LLL comparison or a transition maximizer theorem. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_transition_uniform_failure_lower {m n : ℕ} (hm : 2≤m)
    (hmn : m≤n) (hn : n≤10000*m^2) :
    (1/40001:ℝ)≤1-distinctUniformProbability n m := by
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnR : (n:ℝ)≤10000*(m:ℝ)^2 := by exact_mod_cast hn
  have he : (1/40000:ℝ)≤(m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    nlinarith
  have hb := (distinctUniformProbability_le_exp (by omega) hmn).trans
    (Real.exp_le_exp.mpr (neg_le_neg he))
  have hexp : Real.exp (-(1/40000:ℝ))≤40000/40001 := by
    rw [Real.exp_neg,inv_eq_one_div]
    have ht := Real.add_one_le_exp (1/40000:ℝ)
    have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
      (by norm_num : (0:ℝ)<1/40000+1) ht
    norm_num at h ⊢
    exact h
  linarith

/-- Every bound is derived from the full-probability contender relation.
The reciprocal deviation belongs to the original normalized row law. -/
theorem endpoint_transition_contender_row_bounds {m n : ℕ} (hm : 2≤m)
    (hmn : m≤n) (hn : n≤10000*m^2) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    (∀ i,1/150000<(m:ℝ)*rowSum P i ∧ (m:ℝ)*rowSum P i<32) ∧
    (∑ i,((m:ℝ)*rowSum P i-1)^2)<1024 ∧
    endpointRowReciprocalDeviation P<160000000 := by
  let y : Fin m → ℝ := fun i => (m:ℝ)*rowSum P i
  have hy (i : Fin m) : 0≤y i := mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP.1 i)
  have hs : (∑ i,y i)=m := by
    change (∑ i,(m:ℝ)*rowSum P i)=m
    rw [← Finset.mul_sum,show (∑ i,rowSum P i)=1 from hP.2,mul_one]
  have hprod := endpoint_contender_rowProduct_lower hm hmn hP hcont
  rw [endpointRowProduct_eq_product] at hprod
  have hq := endpoint_transition_uniform_failure_lower hm hmn hn
  have hp : 1/50000<∏ i,y i := lt_of_lt_of_le (by norm_num : (1/50000:ℝ)<1/40001)
    (hq.trans hprod)
  exact ⟨transition_product_coordinate_bounds y hy hs hp,
    transition_product_sq_deviation y hy hs hp,
    transition_product_reciprocal_deviation y hy hs hp⟩

end DittertRybin
