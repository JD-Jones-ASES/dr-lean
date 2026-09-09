import DR.Rectangular.OrderThreeSampling
import Mathlib.Analysis.Real.Sqrt

/-! A quantitative scalar gauge on the entire closed four-row probability simplex. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def orderThreeFourRowWeight (t : ℝ) : ℝ :=
  Real.sqrt (1-(2/3)*(1-t)^2)

noncomputable def orderThreeFourRowGauge (t : ℝ) : ℝ := t*orderThreeFourRowWeight t

noncomputable def orderThreeFourRowVariance (r : Fin 4 → ℝ) : ℝ :=
  ∑ i,(r i-1/4)^2

/-- The square-root argument is bounded away from zero, even at a zero row mass. -/
theorem orderThreeFourRowWeight_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (1/3) ≤ orderThreeFourRowWeight t ∧ orderThreeFourRowWeight t ≤ 1 := by
  have hs : (1-t)^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  constructor
  · apply Real.sqrt_le_sqrt
    linarith
  · unfold orderThreeFourRowWeight
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by nlinarith [sq_nonneg (1-t)]⟩

/-- The supporting quadratic is valid globally; no convexity assertion about the gauge is assumed. -/
theorem orderThreeFourRowGauge_support {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (16*t^2+88*t-3)/32 ≤ Real.sqrt 10 * orderThreeFourRowGauge t := by
  have harg : 0 ≤ 1-(2/3 : ℝ)*(1-t)^2 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hsqrt := Real.sq_sqrt harg
  have hs10 : Real.sqrt (10 : ℝ)^2=10 := Real.sq_sqrt (by norm_num)
  have hleft : 0 ≤ Real.sqrt 10 * orderThreeFourRowGauge t :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg ht0 (Real.sqrt_nonneg _))
  by_cases hnum : 16*t^2+88*t-3 ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)).trans hleft
  have htlo : 3/104 ≤ t := by
    have hsq : t^2 ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
    linarith
  have hchord := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htlo) (sub_nonpos.mpr ht1)
  have hquad : 1328*t^2-1368*t+27 < 0 := by nlinarith only [hchord,ht0]
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (4*t-1)) hquad.le
  have hid : (Real.sqrt 10 * orderThreeFourRowGauge t)^2 - ((16*t^2+88*t-3)/32)^2 =
      -((4*t-1)^2*(1328*t^2-1368*t+27))/3072 := by
    unfold orderThreeFourRowGauge orderThreeFourRowWeight
    rw [mul_pow,mul_pow,hs10,hsqrt]
    ring
  apply le_of_sq_le_sq _ hleft
  nlinarith only [hid,hprod]

/-- Summing the scalar bound gives a quantitative gap above the uniform row gauge. -/
theorem orderThreeFourRowGauge_sum_lower (r : Fin 4 → ℝ) (hr : ∀ i,0 ≤ r i)
    (hmass : ∑ i,r i=1) :
    Real.sqrt 10/4+orderThreeFourRowVariance r/(2*Real.sqrt 10) ≤ ∑ i,orderThreeFourRowGauge (r i) := by
  have hs10 : Real.sqrt (10 : ℝ)^2=10 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hri (i : Fin 4) : r i ≤ 1 := by
    calc
      _ ≤ ∑ j,r j := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
      _ = 1 := hmass
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => orderThreeFourRowGauge_support (hr i) (hri i))
  have hvar : orderThreeFourRowVariance r = (∑ i,r i^2)-1/4 := by
    simp only [orderThreeFourRowVariance, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hmass, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hs : (5/2 : ℝ)+orderThreeFourRowVariance r/2 ≤ Real.sqrt 10*(∑ i,orderThreeFourRowGauge (r i)) := by
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hmass, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith only [hsum,hvar]
  have hscale : (Real.sqrt 10/4+orderThreeFourRowVariance r/(2*Real.sqrt 10))*Real.sqrt 10 =
      5/2+orderThreeFourRowVariance r/2 := by field_simp; nlinarith only [hs10]
  apply (mul_le_mul_iff_left₀ hspos).mp
  rw [hscale]
  nlinarith only [hs]

/-- The row variance is controlled directly by the squared total gauge. -/
theorem orderThreeFourRowGauge_sum_sq_lower (r : Fin 4 → ℝ) (hr : ∀ i,0 ≤ r i)
    (hmass : ∑ i,r i=1) :
    5/8+orderThreeFourRowVariance r/4 ≤ (∑ i,orderThreeFourRowGauge (r i))^2 := by
  have h := orderThreeFourRowGauge_sum_lower r hr hmass
  have hρ : 0 ≤ orderThreeFourRowVariance r := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs10 : Real.sqrt (10 : ℝ)^2=10 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hbase : 0 ≤ Real.sqrt 10/4+orderThreeFourRowVariance r/(2*Real.sqrt 10) := by positivity
  have hsq := pow_le_pow_left₀ hbase h 2
  have hscale := mul_le_mul_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 40)
  field_simp at hscale
  nlinarith [sq_nonneg (orderThreeFourRowVariance r)]

end DittertRybin
