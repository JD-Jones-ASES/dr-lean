import DR.Endpoint.TwoZeroPolynomialBounds

/-! A uniform rational bracket for the unique real cubic root, valid for every
m≥4. Only the bracket signs are needed for the scalar lower bound. -/
namespace DittertRybin

theorem twoZeroCubic_reciprocal {m : ℕ} (hm : 0 < m) :
    twoZeroCubic m (1/(m : ℝ)) = (2*(m : ℝ)^2-5*(m : ℝ)+4)/(m : ℝ)^3 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroCubic
  field_simp
  ring

theorem twoZeroCubic_lowerPoint {m : ℕ} (hm : 0 < m) :
    twoZeroCubic m (1/(m : ℝ)-2/(m : ℝ)^3) =
      -(3*(m : ℝ)^7-2*(m : ℝ)^6-10*(m : ℝ)^5+24*(m : ℝ)^4-
        4*(m : ℝ)^3-40*(m : ℝ)^2+24*(m : ℝ)+32)/(m : ℝ)^9 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroCubic
  field_simp
  ring

/-- Every admitted dimension has an exact, strict root bracket. -/
theorem twoZeroCubic_uniform_bracket {m : ℕ} (hm : 4 ≤ m) :
    0 < 1/(m : ℝ)-2/(m : ℝ)^3 ∧
      1/(m : ℝ)-2/(m : ℝ)^3 < 1/(m : ℝ) ∧
      twoZeroCubic m (1/(m : ℝ)-2/(m : ℝ)^3) < 0 ∧
      0 < twoZeroCubic m (1/(m : ℝ)) := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hM0
  have hz : 0 ≤ (m : ℝ)-4 := by linarith
  have hi : 1/(m : ℝ)-2/(m : ℝ)^3 = ((m : ℝ)^2-2)/(m : ℝ)^3 := by
    field_simp
  refine ⟨?_,?_,?_,?_⟩
  · rw [hi]
    exact div_pos (by nlinarith [sq_nonneg ((m : ℝ)-4)]) (by positivity)
  · have hp : 0 < 2/(m : ℝ)^3 := by positivity
    linarith
  · rw [twoZeroCubic_lowerPoint (by omega)]
    have hid : 3*(m : ℝ)^7-2*(m : ℝ)^6-10*(m : ℝ)^5+24*(m : ℝ)^4-
        4*(m : ℝ)^3-40*(m : ℝ)^2+24*(m : ℝ)+32 =
        3*((m : ℝ)-4)^7+82*((m : ℝ)-4)^6+950*((m : ℝ)-4)^5+
          6064*((m : ℝ)-4)^4+23100*((m : ℝ)-4)^3+
          52648*((m : ℝ)-4)^2+66584*((m : ℝ)-4)+36096 := by ring
    rw [hid]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) (by positivity)
  · rw [twoZeroCubic_reciprocal (by omega)]
    exact div_pos (by nlinarith [sq_nonneg ((m : ℝ)-4)]) (by positivity)

/-- The source's coarse rational floor, on the full two-parameter domain. -/
theorem twoZeroReducedPermanent_coarse_lower {m : ℕ} (hm : 4 ≤ m)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ)) :
    (m.factorial : ℝ)*(twoZeroX m (1/(m : ℝ)-2/(m : ℝ)^3))^(m-2)*
      twoZeroH m (1/(m : ℝ)) ≤ twoZeroReducedPermanent m a b := by
  obtain ⟨hl,hlr,hfl,hfr⟩ := twoZeroCubic_uniform_bracket hm
  exact twoZeroReducedPermanent_lower_of_bracket hm ha hb haM hbM hl.le hlr.le le_rfl hfl.le hfr.le

end DittertRybin
