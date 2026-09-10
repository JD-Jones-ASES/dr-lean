import DR.Endpoint.TwoZeroPolynomialBracket

/-! Exact real polynomial algebra for the infinite two-zero floor. The source
Bernstein positivity is replaced by an elementary coefficient grouping with
an explicit rational margin on the same closed interval. -/
namespace DittertRybin

noncomputable def twoZeroY (q : ℝ) : ℝ := 1-2*q+2*q^2-4*q^4
noncomputable def twoZeroZ (q : ℝ) : ℝ := 1-3*q+3*q^2+q^4-5*q^5+4*q^6
noncomputable def twoZeroLogPolynomial (q : ℝ) : ℝ :=
  256*q^16-960*q^15+3696*q^14-1748*q^13-3684*q^12+2820*q^11+
    5016*q^10-6730*q^9+834*q^8+2334*q^7-606*q^6-840*q^5+
    344*q^4-46*q^3+96*q^2-71*q+3

/-- Elementary grouping gives a stronger-than-needed strictly positive margin. -/
theorem twoZeroLogPolynomial_pos {q : ℝ} (hq : 0 ≤ q) (hq25 : q ≤ 1/25) :
    0 < twoZeroLogPolynomial q := by
  have hq1 : q ≤ 1 := by linarith
  have hp (k : ℕ) (hk : 5 ≤ k) : q^k ≤ q^5 :=
    pow_le_pow_of_le_one hq hq1 hk
  have h6 := hp 6 (by omega)
  have h9 := hp 9 (by omega)
  have h12 := hp 12 (by omega)
  have h13 := hp 13 (by omega)
  have h15 := hp 15 (by omega)
  have hpos : 0 ≤ 256*q^16+3696*q^14+2820*q^11+5016*q^10+
      834*q^8+2334*q^7+344*q^4+96*q^2 := by positivity
  have hgroup : 3-71*q-46*q^3-14568*q^5 ≤ twoZeroLogPolynomial q := by
    unfold twoZeroLogPolynomial
    nlinarith only [h6,h9,h12,h13,h15,hpos]
  have h3 := pow_le_pow_left₀ hq hq25 3
  have h5 := pow_le_pow_left₀ hq hq25 5
  have hc : (0 : ℝ) < 3-71/25-46/25^3-14568/25^5 := by norm_num
  norm_num at h3 h5
  linarith

/-- The actual logarithm arguments satisfy the advertised geometric caps. -/
theorem twoZeroYZ_caps {q : ℝ} (hq : 0 ≤ q) (hq25 : q ≤ 1/25) :
    0 ≤ 1-twoZeroY q ∧ 1-twoZeroY q ≤ 2*q ∧
      0 ≤ 1-twoZeroZ q ∧ 1-twoZeroZ q ≤ 3*q := by
  have hq1 : q ≤ 1 := by linarith
  have h1 : 0 ≤ 1-q := by linarith
  have h4 : 0 ≤ 1-4*q := by linarith
  have hsq := pow_le_pow_left₀ hq hq25 2
  have hsq1 : 0 ≤ 1-2*q^2 := by norm_num at hsq; linarith
  have hvpos : 0 ≤ 2*q*(1-q+2*q^3) := by positivity
  have hvupper : 0 ≤ 2*q^2*(1-2*q^2) := by positivity
  have hpow : q^4 ≤ q := by simpa using pow_le_pow_of_le_one hq hq1 (by norm_num : 1 ≤ 4)
  have hterm : q^4*(1-4*q) ≤ q := by
    have ht := mul_le_mul_of_nonneg_left (show 1-4*q ≤ 1 by linarith) (pow_nonneg hq 4)
    nlinarith only [ht,hpow]
  have hwpos : 0 ≤ (1-q)*(3*q-q^4*(1-4*q)) := by
    apply mul_nonneg h1
    linarith
  have hwupper : 0 ≤ 3*q^2+q^4*(1-q)*(1-4*q) := by positivity
  unfold twoZeroY twoZeroZ
  constructor
  · nlinarith only [hvpos]
  constructor
  · nlinarith only [hvupper]
  constructor
  · nlinarith only [hwpos]
  · nlinarith only [hwupper]

noncomputable def twoZeroLogLowerY (q : ℝ) : ℝ :=
  let v := 1-twoZeroY q;
  -v-v^2/2-v^3/3-v^4/(4*(1-2*q))
noncomputable def twoZeroLogLowerZ (q : ℝ) : ℝ :=
  let w := 1-twoZeroZ q;
  -w-w^2/2-w^3/(3*(1-3*q))
noncomputable def twoZeroLogLowerPlus (q : ℝ) : ℝ := q-q^2/2+q^3/3-q^4/4

/-- Source equation (11), with every rational denominator retained. -/
theorem twoZeroLogLower_identity {q : ℝ} (hq : q ≠ 0)
    (h2 : 1-2*q ≠ 0) (h3 : 1-3*q ≠ 0) :
    (1/q-2)*twoZeroLogLowerY q+twoZeroLogLowerZ q+(2/q)*twoZeroLogLowerPlus q-q^2/4 =
      q^2*twoZeroLogPolynomial q/(12*(1-3*q)) := by
  have h2' : 1-q*2 ≠ 0 := by simpa only [mul_comm q 2] using h2
  have h3' : 1-q*3 ≠ 0 := by simpa only [mul_comm q 3] using h3
  unfold twoZeroLogLowerY twoZeroLogLowerZ twoZeroLogLowerPlus twoZeroY twoZeroZ twoZeroLogPolynomial
  field_simp [hq,h2,h3,h2',h3']
  ring

end DittertRybin
