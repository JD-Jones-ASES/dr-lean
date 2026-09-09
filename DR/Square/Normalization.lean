import DR.EndpointIdentity
import DR.Rectangular.OrderTwo

/-!
# Equivalence of the Rybin and Dittert normalizations

For positive n, the maps `P ↦ n • P` and `A ↦ n⁻¹ • A` are inverse
bijections between the entire probability simplex and the nonnegative
mass-n simplex. They preserve the uniform equality case, including on the
boundary. Thus the square endpoint maximization statement is exactly
Dittert's statement, rather than merely a consequence for balanced matrices.
-/

namespace DittertRybin

open scoped BigOperators

theorem totalMass_smul {m n : ℕ} (P : Board m n) (c : ℝ) :
    totalMass (c • P) = c * totalMass P := by
  simp [totalMass, rowSum, Finset.mul_sum]

theorem dittertConstant_pos {n : ℕ} (hn : 0 < n) : 0 < dittertConstant n := by
  exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    (pow_pos (Nat.cast_pos.mpr hn) n)

theorem uniformSeparationValue_endpoint (n : ℕ) :
    uniformSeparationValue n n n = dittertConstant n * (2 - dittertConstant n) := by
  simp only [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial_self,
    dittertConstant]
  ring

theorem smul_uniformBoard {n : ℕ} (hn : 0 < n) :
    (n : ℝ) • uniformBoard n n = uniformDittertMatrix n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  ext i j
  simp only [uniformBoard, uniformDittertMatrix, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem inv_smul_uniformDittertMatrix (n : ℕ) :
    (n : ℝ)⁻¹ • uniformDittertMatrix n = uniformBoard n n := by
  ext i j
  simp [uniformDittertMatrix, uniformBoard, mul_inv_rev]

theorem normalize_eq_uniform_iff {n : ℕ} (hn : 0 < n) (A : Board n n) :
    (n : ℝ)⁻¹ • A = uniformBoard n n ↔ A = uniformDittertMatrix n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  constructor
  · intro h
    have h' := congrArg (fun P : Board n n => (n : ℝ) • P) h
    simpa [smul_smul, hn0, smul_uniformBoard hn] using h'
  · intro h
    rw [h, inv_smul_uniformDittertMatrix]

theorem scale_eq_uniform_iff {n : ℕ} (hn : 0 < n) (P : Board n n) :
    (n : ℝ) • P = uniformDittertMatrix n ↔ P = uniformBoard n n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  constructor
  · intro h
    have h' := congrArg (fun A : Board n n => (n : ℝ)⁻¹ • A) h
    simpa [smul_smul, hn0, inv_smul_uniformDittertMatrix] using h'
  · intro h
    rw [h, smul_uniformBoard hn]

theorem normalize_isProbability {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n) :
    IsProbability ((n : ℝ)⁻¹ • A) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  constructor
  · intro i j
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (hA i j)
  · rw [totalMass_smul, hmass, inv_mul_cancel₀ hn0]

/-- The square P2 and Dittert statements are equivalent, with their exact equality cases. -/
theorem uniformMaximizer_iff_dittertMaximizer {n : ℕ} (hn : 0 < n) :
    UniformMaximizer n n n ↔ DittertMaximizer n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hg := dittertConstant_pos hn
  have heq (a b : ℝ) : dittertConstant n * a = dittertConstant n * b ↔ a = b :=
    ⟨mul_left_cancel₀ hg.ne', congrArg (fun x => dittertConstant n * x)⟩
  constructor
  · intro h A hA hmass
    have hP := h ((n : ℝ)⁻¹ • A) (normalize_isProbability hn A hA hmass)
    have hid : separationProbability ((n : ℝ)⁻¹ • A) n =
        dittertConstant n * dittertFunctional A := by
      rw [separationProbability_eq_dittert hn]
      simp [smul_smul, hn0]
    rw [hid, uniformSeparationValue_endpoint] at hP
    exact ⟨(mul_le_mul_iff_right₀ hg).mp hP.1,
      (heq _ _).symm.trans (hP.2.trans (normalize_eq_uniform_iff hn A))⟩
  · intro h P hP
    have hA : ∀ i j, 0 ≤ ((n : ℝ) • P) i j := by
      intro i j
      exact mul_nonneg (Nat.cast_nonneg n) (hP.1 i j)
    have hmass : totalMass ((n : ℝ) • P) = n := by
      rw [totalMass_smul, hP.2, mul_one]
    have hD := h ((n : ℝ) • P) hA hmass
    rw [separationProbability_eq_dittert hn, uniformSeparationValue_endpoint]
    exact ⟨(mul_le_mul_iff_right₀ hg).mpr hD.1,
      (heq _ _).trans (hD.2.trans (scale_eq_uniform_iff hn P))⟩

/-- Dittert's inequality and unique equality case in order two. -/
theorem dittert_order_two : DittertMaximizer 2 :=
  (uniformMaximizer_iff_dittertMaximizer (by decide)).mp
    (uniform_maximum_order_two_of_pos (by decide) (by decide))

/-- The order-one Dittert simplex consists of the single matrix with entry one. -/
theorem dittert_order_one : DittertMaximizer 1 := by
  intro A _ hmass
  have hentry : A 0 0 = 1 := by simpa [totalMass, rowSum] using hmass
  have hu : A = uniformDittertMatrix 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa [uniformDittertMatrix] using hentry
  rw [hu]
  norm_num [dittertFunctional, rowSum, colSum, uniformDittertMatrix,
    dittertConstant, Nat.factorial, Matrix.permanent]

end DittertRybin
