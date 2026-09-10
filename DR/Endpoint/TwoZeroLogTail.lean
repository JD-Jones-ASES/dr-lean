import DR.Endpoint.TwoZeroLogBounds
import DR.Endpoint.TwoZeroLogAlgebra
import DR.Endpoint.BoundaryPermanent

/-! The all-dimension scalar improvement over the one-zero permanent floor.
This theorem concerns the explicit two-parameter formula; its actual matrix
interpretation is supplied independently by the two-zero face reduction. -/
namespace DittertRybin

/-- The logarithmic comparison has a strict positive margin on the complete
real interval, with no sampled or certificate hypothesis. -/
theorem twoZero_logarithmic_margin {q : ℝ} (hq : 0 < q) (hq25 : q ≤ 1/25) :
    q^2/4 < (1/q-2)*Real.log (twoZeroY q)+Real.log (twoZeroZ q)+
      (2/q)*Real.log (1+q) := by
  obtain ⟨hv0,hv,hz0,hz⟩ := twoZeroYZ_caps hq.le hq25
  have h2 : 2*q < 1 := by linarith
  have h3 : 3*q < 1 := by linarith
  have hY := twoZero_log_one_sub_quartic_cap hv0 hv h2
  have hZ := twoZero_log_one_sub_cubic_cap hz0 hz h3
  have hP := twoZero_log_one_add_quartic hq.le
  simp only [sub_sub_cancel] at hY hZ
  change twoZeroLogLowerY q ≤ Real.log (twoZeroY q) at hY
  change twoZeroLogLowerZ q ≤ Real.log (twoZeroZ q) at hZ
  change twoZeroLogLowerPlus q ≤ Real.log (1+q) at hP
  have hcoef : 0 ≤ 1/q-2 := by
    have hi : 2 ≤ 1/q := (le_div_iff₀ hq).mpr (by linarith)
    linarith
  have hYM := mul_le_mul_of_nonneg_left hY hcoef
  have hPM := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2/q by positivity)
  have hi := twoZeroLogLower_identity hq.ne' (by linarith) (by linarith)
  have hpos : 0 < q^2*twoZeroLogPolynomial q/(12*(1-3*q)) := by
    have hp := twoZeroLogPolynomial_pos hq.le hq25
    have hd : 0 < 1-3*q := by linarith
    positivity
  linarith only [hYM,hZ,hPM,hi,hpos]

noncomputable def twoZeroCoarseRatio (m : ℕ) : ℝ :=
  (twoZeroY (1/(m : ℝ)))^(m-2)*twoZeroZ (1/(m : ℝ))*
    (1+1/(m : ℝ))^(2*m)

theorem twoZeroCoarseRatio_gt {m : ℕ} (hm : 25 ≤ m) :
    1+1/(4*(m : ℝ)^2) < twoZeroCoarseRatio m := by
  have hM : (25 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hq : 0 < 1/(m : ℝ) := by positivity
  have hq25 : 1/(m : ℝ) ≤ 1/25 := one_div_le_one_div_of_le (by norm_num) hM
  obtain ⟨_,hY,_,hZ⟩ := twoZeroYZ_caps hq.le hq25
  have hy : 0 < twoZeroY (1/(m : ℝ)) := by linarith
  have hz : 0 < twoZeroZ (1/(m : ℝ)) := by linarith
  have hp : 0 < 1+1/(m : ℝ) := by positivity
  have hratio : 0 < twoZeroCoarseRatio m := by unfold twoZeroCoarseRatio; positivity
  have hlog : Real.log (twoZeroCoarseRatio m) =
      (1/(1/(m : ℝ))-2)*Real.log (twoZeroY (1/(m : ℝ)))+
        Real.log (twoZeroZ (1/(m : ℝ)))+(2/(1/(m : ℝ)))*Real.log (1+1/(m : ℝ)) := by
    unfold twoZeroCoarseRatio
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hy.ne') hz.ne') (pow_ne_zero _ hp.ne'),
      Real.log_mul (pow_ne_zero _ hy.ne') hz.ne',Real.log_pow,Real.log_pow,
      Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
  have h := twoZero_logarithmic_margin hq hq25
  rw [← hlog] at h
  have he := Real.log_le_sub_one_of_pos hratio
  have hi : (1/(m : ℝ))^2/4 = 1/(4*(m : ℝ)^2) := by ring
  rw [hi] at h
  linarith


theorem twoZeroX_coarse_normalization {m : ℕ} (hm : 0 < m) :
    twoZeroX m (1/(m : ℝ)-2/(m : ℝ)^3) =
      (1/(m : ℝ))*twoZeroY (1/(m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroX twoZeroY
  field_simp
  ring

theorem twoZeroH_reciprocal_normalization {m : ℕ} (hm : 0 < m) :
    twoZeroH m (1/(m : ℝ)) = (1/(m : ℝ))^2*twoZeroZ (1/(m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroH twoZeroX twoZeroZ
  field_simp
  ring

/-- The factor is normalized by the one-zero boundary floor in dimension m+2. -/
theorem twoZeroCoarseRatio_normalization {m : ℕ} (hm : 2 ≤ m) :
    (m.factorial : ℝ)*(twoZeroX m (1/(m : ℝ)-2/(m : ℝ)^3))^(m-2)*
      twoZeroH m (1/(m : ℝ)) = boundaryPermanentFloor (m+2)*twoZeroCoarseRatio m := by
  have hM0 : (0 : ℝ) < m := by positivity
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hM0
  have hM1 : (m : ℝ)+1 ≠ 0 := by positivity
  have hbase : ((m : ℝ)/((m : ℝ)+1)^2)*(1+1/(m : ℝ))^2 = 1/(m : ℝ) := by
    field_simp
  have hp : ((m : ℝ)/((m : ℝ)+1)^2)^m*(1+1/(m : ℝ))^(2*m) = (1/(m : ℝ))^m := by
    rw [pow_mul,← mul_pow,hbase]
  have hmu : boundaryPermanentFloor (m+2) =
      (m.factorial : ℝ)*((m : ℝ)/((m : ℝ)+1)^2)^m := by
    unfold boundaryPermanentFloor
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
    congr 2
    ring
  rw [twoZeroX_coarse_normalization (by omega),twoZeroH_reciprocal_normalization (by omega),
    hmu,twoZeroCoarseRatio,mul_pow]
  have hqpow : (1/(m : ℝ))^(m-2)*(1/(m : ℝ))^2 = (1/(m : ℝ))^m := by
    rw [← pow_add,Nat.sub_add_cancel hm]
  calc
    _ = (m.factorial : ℝ)*((1/(m : ℝ))^(m-2)*(1/(m : ℝ))^2)*
        (twoZeroY (1/(m : ℝ)))^(m-2)*twoZeroZ (1/(m : ℝ)) := by ring
    _ = (m.factorial : ℝ)*(1/(m : ℝ))^m*(twoZeroY (1/(m : ℝ)))^(m-2)*
        twoZeroZ (1/(m : ℝ)) := by rw [hqpow]
    _ = _ := by rw [← hp]; ring

/-- Strict all-dimension scalar improvement, retaining every boundary parameter. -/
theorem twoZeroReducedPermanent_tail_gap {m : ℕ} (hm : 25 ≤ m)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ)) :
    boundaryPermanentFloor (m+2)*(1+1/(4*(m : ℝ)^2)) < twoZeroReducedPermanent m a b := by
  have hmu := boundaryPermanentFloor_pos (by omega : 3 ≤ m+2)
  have h := mul_lt_mul_of_pos_left (twoZeroCoarseRatio_gt hm) hmu
  rw [← twoZeroCoarseRatio_normalization (by omega : 2 ≤ m)] at h
  exact h.trans_le (twoZeroReducedPermanent_coarse_lower (by omega : 4 ≤ m) ha hb haM hbM)

end DittertRybin
