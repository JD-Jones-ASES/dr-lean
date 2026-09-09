import DR.Rectangular.FourRowMarginalBounds

/-!
# A quantitative positive region for the actual four-row kernel

Every probability marginal with squared deviation at most 1/40 satisfies
the uniform lower bound 97/5792 on its leading-kernel quadratic form. The
coordinate and product bounds are proved from that closed neighborhood.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates

theorem fourRowReferenceQuadratic_lower (s x : Fin 4 → ℝ)
    (hsum : ∑ i, s i = 1) (hnear : fourRowMarginalVariance s ≤ 1 / 40) :
    (1 / 32 : ℝ) * (∑ i, x i ^ 2) ≤ fourRowReferenceQuadratic s x := by
  have hcoord := fourRowMarginalVariance_coordinates s hsum hnear
  have hp := fourRow_product_lower_of_near s hsum hnear
  have hterm (i : Fin 4) : (1 / 32 : ℝ) * x i ^ 2 ≤
      (2 * ∏ j, s j) * (x i / s i) ^ 2 := by
    have hsi : 0 < s i := lt_trans (by norm_num) (hcoord i).1
    have hsi2 : s i ^ 2 ≤ 4 / 25 := by nlinarith [(hcoord i).2]
    have hcoef : (1 / 32 : ℝ) ≤ (2 * ∏ j, s j) / s i ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hsi)).mpr
      nlinarith
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (x i))
    calc
      _ ≤ (2 * ∏ j, s j) / s i ^ 2 * x i ^ 2 := h
      _ = _ := by rw [div_pow]; ring
  have hsumterm := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  simp only [← Finset.mul_sum] at hsumterm
  exact hsumterm.trans (le_add_of_nonneg_right (sq_nonneg (∑ i, x i)))

theorem fourRowLeadingKernel_near_lower (s x : Fin 4 → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hsum : ∑ i, s i = 1)
    (hnear : fourRowMarginalVariance s ≤ 1 / 40) :
    (97 / 5792 : ℝ) * (∑ i, x i ^ 2) ≤ quadraticValue (fourRowLeadingKernel s) x := by
  have hcoord := fourRowMarginalVariance_coordinates s hsum hnear
  have hspos : ∀ i, 0 < s i := fun i => lt_trans (by norm_num) (hcoord i).1
  have hprod0 : 0 < ∏ i, s i := Finset.prod_pos fun i _ => hspos i
  have hprod := fourRow_product_le_uniform s hs hsum
  have hq := fourRowMarginalVariance_squareSum s hsum
  have hden0 : 0 < (∑ i, s i ^ 2) + 2 * ∏ i, s i := by positivity
  have hden : (∑ i, s i ^ 2) + 2 * ∏ i, s i ≤ 181 / 640 := by linarith
  have hrecip := one_div_le_one_div_of_le hden0 hden
  norm_num at hrecip
  have hfactor : (97 / 181 : ℝ) ≤ 1 / ((∑ i, s i ^ 2) + 2 * ∏ i, s i) - 3 := by
    simp only [one_div]
    linarith
  have hA := fourRowReferenceQuadratic_lower s x hsum hnear
  have hA0 : 0 ≤ fourRowReferenceQuadratic s x :=
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg (x i))).trans hA
  calc
    (97 / 5792 : ℝ) * (∑ i, x i ^ 2) = (97 / 181 : ℝ) * ((1 / 32 : ℝ) * (∑ i, x i ^ 2)) := by ring
    _ ≤ (97 / 181 : ℝ) * fourRowReferenceQuadratic s x :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ (1 / ((∑ i, s i ^ 2) + 2 * ∏ i, s i) - 3) * fourRowReferenceQuadratic s x :=
      mul_le_mul_of_nonneg_right hfactor hA0
    _ ≤ _ := fourRowLeadingKernel_rank_one_lower s x hspos hsum

end DittertRybin
