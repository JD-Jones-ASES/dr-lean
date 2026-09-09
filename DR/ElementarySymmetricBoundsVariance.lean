import DR.ElementarySymmetricBounds

/-! Quantitative marginal concentration from elementary-symmetric success. -/

namespace DittertRybin
open scoped BigOperators

/-- The elementary comparison controls variance on the entire closed simplex. -/
theorem marginalVariance_le_of_elementary_success {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d)
    {epsilon : ℝ} (_he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (he : 1-epsilon ≤ normalizedElementarySuccess x k) :
    marginalVariance x ≤ 2*((d:ℝ)-1)*epsilon/((d:ℝ)*k*(1-epsilon)) := by
  have hd : 2 ≤ d := hk.trans hkd
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0:ℝ) < (d:ℝ)-1 := by linarith [show (2:ℝ) ≤ d by exact_mod_cast hd]
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hε : 0 < 1-epsilon := by linarith
  have hEk : 0 < normalizedElementarySuccess x k := hε.trans_le he
  have hm := normalizedElementarySuccess_maclaurin_two hx hk hkd
  have hlower : (1-epsilon)^2 ≤ normalizedElementarySuccess x 2^k := by
    have hsq : (1-epsilon)^2 ≤ normalizedElementarySuccess x k^2 := by nlinarith
    exact hsq.trans hm
  have hE2 : 0 < normalizedElementarySuccess x 2 := by
    have hn := normalizedElementarySuccess_nonneg hx 2
    by_contra h
    have hz : normalizedElementarySuccess x 2 = 0 := by linarith
    rw [hz,zero_pow (by omega : k ≠ 0)] at hlower
    nlinarith
  have hlog := Real.log_le_log (sq_pos_of_pos hε) hlower
  rw [Real.log_pow,Real.log_pow] at hlog
  have hupper := Real.log_le_sub_one_of_pos hE2
  rw [normalizedElementarySuccess_two hd hs] at hupper hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hloglower := Real.one_sub_inv_le_log_of_pos hε
  have hbound : (k:ℝ)*((d:ℝ)/(d-1)*marginalVariance x) ≤
      2*((1-epsilon)⁻¹-1) := by
    nlinarith [mul_le_mul_of_nonneg_left hupper hk0.le]
  have hscale := mul_le_mul_of_nonneg_right hbound (mul_nonneg hd1.le hε.le)
  have hid : 2*((1-epsilon)⁻¹-1)*((d-1)*(1-epsilon)) =
      2*(d-1)*epsilon := by field_simp; ring
  have hidL : (k:ℝ)*((d:ℝ)/(d-1)*marginalVariance x)*((d-1)*(1-epsilon)) =
      marginalVariance x*((d:ℝ)*k*(1-epsilon)) := by field_simp
  rw [hid,hidL] at hscale
  exact (le_div_iff₀ (mul_pos (mul_pos hd0 hk0) hε)).mpr hscale

theorem elementarySymmetric_const (d k : ℕ) (a : ℝ) :
    elementarySymmetric (fun _ : Fin d => a) k = (d.choose k:ℝ)*a^k := by
  classical
  rw [elementarySymmetric_eq_powerset_sum]
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ _i ∈ S, a) =
        ∑ _S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, a^k := by
      apply Finset.sum_congr rfl
      intro S hS
      simp only [Finset.prod_const,(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by simp [Finset.card_powersetCard]

theorem normalizedElementarySuccess_uniform {d k : ℕ} (hd : 0 < d) (hkd : k ≤ d) :
    normalizedElementarySuccess (fun _ : Fin d => 1/(d:ℝ)) k = 1 := by
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc : (d.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkd).ne'
  rw [normalizedElementarySuccess,elementaryMean,elementarySymmetric_const]
  field_simp
  rw [← mul_pow]
  simp [hd0]

/-- Equality in the closed-simplex Maclaurin bound is exactly uniformity. -/
theorem normalizedElementarySuccess_eq_one_iff {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d) :
    normalizedElementarySuccess x k = 1 ↔ ∀ i, x i = 1/(d:ℝ) := by
  constructor
  · intro he i
    have hV := marginalVariance_le_of_elementary_success hx hs hk hkd
      (epsilon := 0) (by norm_num) (by norm_num) (by simp [he])
    have hz : marginalVariance x = 0 := by
      have hn := marginalVariance_nonneg x
      simp only [mul_zero,zero_div] at hV
      exact le_antisymm hV hn
    have hi : (x i-1/(d:ℝ))^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j-1/(d:ℝ)))).mp hz i
        (Finset.mem_univ i)
    nlinarith
  · intro he
    have hxU : x = fun _ : Fin d => 1/(d:ℝ) := funext he
    rw [hxU]
    exact normalizedElementarySuccess_uniform (by omega) hkd

end DittertRybin
