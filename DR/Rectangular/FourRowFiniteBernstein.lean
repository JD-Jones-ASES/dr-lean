import DR.Certificates.BernsteinTransform
import DR.Certificates.Gram
import Mathlib.Algebra.Order.Star.Real

/-!
# Matrix Bernstein soundness for the finite four-row families

The literal power coefficients determine every matrix entry. Their exact
affine and Bernstein transforms give a convex combination of coefficient
matrices on the entire closed interval. Positive definiteness of all those
matrices therefore proves positive definiteness of the polynomial matrix,
including both endpoints. The application still has to supply every finite
coefficient check and the actual block identity.
-/

namespace DittertRybin.Certificates

noncomputable section
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem quadraticValue_weighted_matrix_sum (w : κ → ℝ)
    (Q : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    quadraticValue (fun i j => ∑ k, w k * Q k i j) x =
      ∑ k, w k * quadraticValue (Q k) x := by
  unfold quadraticValue
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, x i * (w k * Q k i j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, x i * (w k * Q k i j) * x j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Nonnegative weights of total one preserve strict matrix positivity even
when some weights vanish, as they do at the interval endpoints. -/
theorem posDef_weighted_matrix_sum (w : κ → ℝ) (Q : κ → Matrix ι ι ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hQ : ∀ k, (Q k).PosDef) :
    (Matrix.of (fun i j => ∑ k, w k * Q k i j)).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    apply Finset.sum_congr rfl
    intro k _
    rw [(Matrix.isHermitian_iff_isSymm.mp (hQ k).isHermitian).apply]
  · intro x hx
    have hpos (k : κ) : 0 < quadraticValue (Q k) x := by
      simpa only [quadraticValue_eq_dotProduct, star_trivial] using
        (hQ k).dotProduct_mulVec_pos hx
    have hex : ∃ k, 0 < w k := by
      by_contra h
      push Not at h
      have hz : ∑ k, w k = 0 := Finset.sum_eq_zero fun k _ => le_antisymm (h k) (hw k)
      linarith
    obtain ⟨k, hk⟩ := hex
    have hp : 0 < quadraticValue (fun i j => ∑ k, w k * Q k i j) x := by
      rw [quadraticValue_weighted_matrix_sum]
      exact Finset.sum_pos' (fun k _ => mul_nonneg (hw k) (hpos k).le)
        ⟨k, Finset.mem_univ k, mul_pos hk (hpos k)⟩
    change 0 < quadraticValue (Matrix.of (fun i j => ∑ k, w k * Q k i j)) x at hp
    rw [quadraticValue_eq_dotProduct] at hp
    simpa only [star_trivial] using hp

/-- Evaluation of a full finite rational power-coefficient matrix table. -/
def fourRowFiniteMatrixPolynomial {d : ℕ}
    (p : Fin (d + 1) → Matrix ι ι ℚ) (u : ℝ) : Matrix ι ι ℝ :=
  fun i j => rationalEval (fun _ : Fin 1 => u) (powerPolynomial (fun k => p k i j))

/-- The exact entrywise affine power-to-Bernstein coefficient transform. -/
def fourRowFiniteMatrixBernstein {d : ℕ} (lo hi : ℚ)
    (p : Fin (d + 1) → Matrix ι ι ℚ) (k : Fin (d + 1)) : Matrix ι ι ℚ :=
  fun i j => powerToBernstein (affinePowerCoefficients lo hi (fun a => p a i j)) k

omit [Fintype ι] in
theorem fourRowFiniteMatrixPolynomial_eval {d : ℕ}
    (p : Fin (d + 1) → Matrix ι ι ℚ) (u : ℝ) (i j : ι) :
    fourRowFiniteMatrixPolynomial p u i j = ∑ k, (p k i j : ℝ) * u ^ (k : ℕ) := by
  simp [fourRowFiniteMatrixPolynomial, rationalEval, powerPolynomial]

omit [Fintype ι] in
/-- This identity is derived from the proved scalar transform, not interpolation. -/
theorem fourRowFiniteMatrixPolynomial_bernstein {d : ℕ} (lo hi : ℚ)
    (p : Fin (d + 1) → Matrix ι ι ℚ) (t : ℝ) :
    fourRowFiniteMatrixPolynomial p ((lo : ℝ) + ((hi : ℝ) - lo) * t) =
      fun i j => ∑ k : Fin (d + 1), bernsteinWeight d k t *
        (fourRowFiniteMatrixBernstein lo hi p k i j : ℝ) := by
  ext i j
  change rationalEval _ (powerPolynomial _) = _
  calc
    _ = rationalEval (fun _ : Fin 1 => t)
        (affineNormalize (fun _ => lo) (fun _ => hi)
          (powerPolynomial (fun k => p k i j))) := by
      rw [rationalEval_affineNormalize]
    _ = _ := by
      rw [affineNormalize_powerPolynomial, powerPolynomial_eq_tensorPolynomial,
        tensorPolynomial_one]
      simp only [rationalEval, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
        MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [fourRowFiniteMatrixBernstein, bernsteinWeight]
      norm_cast
      ring

theorem fourRowFiniteMatrixPolynomial_posDef {d : ℕ} (lo hi : ℚ)
    (p : Fin (d + 1) → Matrix ι ι ℚ) (hwidth : lo < hi)
    (hcoeff : ∀ k, ((fourRowFiniteMatrixBernstein lo hi p k).map
      (fun q : ℚ => (q : ℝ))).PosDef)
    (u : ℝ) (hu : (lo : ℝ) ≤ u ∧ u ≤ hi) :
    (fourRowFiniteMatrixPolynomial p u).PosDef := by
  let t := (u - lo) / ((hi : ℝ) - lo)
  have hd : (0 : ℝ) < (hi : ℝ) - lo := sub_pos.mpr (Rat.cast_lt.mpr hwidth)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hu.1) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (sub_le_sub_right hu.2 _)
  have he : (lo : ℝ) + ((hi : ℝ) - lo) * t = u := by
    dsimp [t]
    field_simp
    ring
  rw [← he, fourRowFiniteMatrixPolynomial_bernstein]
  exact posDef_weighted_matrix_sum (fun k : Fin (d + 1) => bernsteinWeight d k t)
    (fun k => (fourRowFiniteMatrixBernstein lo hi p k).map (fun q : ℚ => (q : ℝ)))
    (fun k => bernsteinWeight_nonneg _ _ ht ht1) (bernsteinWeight_sum d t) hcoeff

/-- A proved positive clearing factor transfers the certified matrix back to
the literal rational-function block. Its entry identity is required explicitly. -/
theorem fourRowFiniteMatrixPolynomial_cleared_posDef {d : ℕ} (lo hi : ℚ)
    (p : Fin (d + 1) → Matrix ι ι ℚ) (hwidth : lo < hi)
    (hcoeff : ∀ k, ((fourRowFiniteMatrixBernstein lo hi p k).map
      (fun q : ℚ => (q : ℝ))).PosDef)
    (u : ℝ) (hu : (lo : ℝ) ≤ u ∧ u ≤ hi) (D : ℝ) (hD : 0 < D)
    (B : Matrix ι ι ℝ) (hidentity : fourRowFiniteMatrixPolynomial p u = D • B) :
    B.PosDef := by
  have hp := fourRowFiniteMatrixPolynomial_posDef lo hi p hwidth hcoeff u hu
  rw [hidentity] at hp
  have h := hp.smul (inv_pos.mpr hD)
  simpa only [smul_smul, inv_mul_cancel₀ hD.ne', one_smul] using h

end
end DittertRybin.Certificates
