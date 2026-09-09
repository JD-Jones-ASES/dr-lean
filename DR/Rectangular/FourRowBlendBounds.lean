import DR.Rectangular.FourRowCorrection

/-! The positive quadratic floor after deleting two columns of a contender. -/

namespace DittertRybin
open scoped BigOperators
open Certificates

theorem fourRowBlendKernel_quadratic_decomposition {n : ℕ} (T : Board 4 n)
    (hm : totalMass T ≠ 0) (x : Fin 4 → ℝ) :
    quadraticValue (fourRowBlendKernel T) x =
      (totalMass T ^ 2 / 2) * quadraticValue
        (fourRowLeadingKernel (fun r => rowSum T r / totalMass T)) x -
      (fourRowColumnSquareMass T / 2) * (∑ i, x i) ^ 2 +
      quadraticValue (fourRowComplementCorrection T) x := by
  unfold quadraticValue
  simp_rw [fourRowBlendKernel_decomposition T hm, mul_add, add_mul, mul_sub, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 2
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem fourRow_sum_sq_bound (x : Fin 4 → ℝ) : (∑ i, x i) ^ 2 ≤ 4 * ∑ i, x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun _ => (1 : ℝ))
  simpa [mul_comm] using h

/-- The exact row-neighborhood hypothesis and actual column square mass control the kernel. -/
theorem fourRowBlendKernel_lower {n : ℕ} (T : Board 4 n)
    (hT : ∀ i j, 0 ≤ T i j) (hm : 0 < totalMass T)
    (hnear : fourRowMarginalVariance (fun i => rowSum T i / totalMass T) ≤ 1 / 40)
    (x : Fin 4 → ℝ) :
    ((totalMass T ^ 2 / 2) * (97 / 5792) - (7 / 3) * fourRowColumnSquareMass T) *
      (∑ i, x i ^ 2) ≤ quadraticValue (fourRowBlendKernel T) x := by
  have hs : ∀ i, 0 ≤ rowSum T i / totalMass T := fun i => div_nonneg (rowSum_nonneg hT i) hm.le
  have hsum : ∑ i, rowSum T i / totalMass T = 1 := by
    rw [← Finset.sum_div]
    change totalMass T / totalMass T = 1
    exact div_self (ne_of_gt hm)
  have hB := fourRowLeadingKernel_near_lower _ x hs hsum hnear
  have hBscale := mul_le_mul_of_nonneg_left hB
    (div_nonneg (sq_nonneg (totalMass T)) (by norm_num : (0 : ℝ) ≤ 2))
  have hH := fourRowComplementCorrection_quadratic_lower T hT x
  have halpha : 0 ≤ fourRowColumnSquareMass T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hJ := mul_le_mul_of_nonneg_left (fourRow_sum_sq_bound x) (div_nonneg halpha (by norm_num : (0 : ℝ) ≤ 2))
  rw [fourRowBlendKernel_quadratic_decomposition T (ne_of_gt hm) x]
  nlinarith

/-- The retained analytic constants give a positive floor, on all boundary supports. -/
theorem fourRowBlendKernel_uniform_floor {n : ℕ} (T : Board 4 n)
    (hT : ∀ i j, 0 ≤ T i j) (hm : 493 / 500 ≤ totalMass T)
    (halpha : fourRowColumnSquareMass T ≤ 7 / 2500)
    (hnear : fourRowMarginalVariance (fun i => rowSum T i / totalMass T) ≤ 1 / 40)
    (x : Fin 4 → ℝ) :
    (13965659 / 8688000000 : ℝ) * (∑ i, x i ^ 2) ≤
      quadraticValue (fourRowBlendKernel T) x := by
  have hmpos : 0 < totalMass T := lt_of_lt_of_le (by norm_num) hm
  have hm2 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 493 / 500) hm
  have hcoef : (13965659 / 8688000000 : ℝ) ≤
      (totalMass T ^ 2 / 2) * (97 / 5792) - (7 / 3) * fourRowColumnSquareMass T := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
    (fourRowBlendKernel_lower T hT hmpos hnear x)

end DittertRybin
