import DR.Rectangular.ThreeRowCellLine

/-! The exact three-row gradient and full-simplex support comparisons on every 3-by-N board. -/

namespace DittertRybin
open scoped BigOperators

theorem hasDerivAt_separationProbability_threeRowAddCell {n : ℕ} (P : Board 3 n)
    (a : Fin 3) (b : Fin n) :
    HasDerivAt (fun t : ℝ => separationProbability (threeRowAddCell P a b t) 3)
      (separationGradient P 3 a b) 0 := by
  have h := hasDerivAt_separationProbability_line P
    (fun i j => if (i, j) = (a, b) then 1 else 0) 3
  unfold threeRowAddCell
  simpa [Prod.mk.injEq, ite_and] using h

/-- Identification with the actual finite-sampling derivative, including zero entries. -/
theorem separationGradient_threeRow {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n) :
    separationGradient P 3 a b = 3 * (totalMass P ^ 2 - ∑ j, colSum P j ^ 2) +
      6 * threeRowReducedGradient P a b := by
  let d := 3 * (totalMass P ^ 2 - ∑ j, colSum P j ^ 2) + 6 * threeRowReducedGradient P a b
  have h := hasDerivAt_separationProbability_threeRowAddCell P a b
  have hf : (fun t : ℝ => separationProbability (threeRowAddCell P a b t) 3) =
      fun t => separationProbability P 3 + d * t := by
    funext t
    exact separationProbability_threeRow_addCell P a b t
  rw [hf] at h
  have hd : HasDerivAt (fun t : ℝ => separationProbability P 3 + d * t) d 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul d).const_add (separationProbability P 3)
  exact h.unique hd

/-- Every missing target cell remains subject to this inequality. -/
theorem IsSeparationGlobalMax.threeRow_gradient_le {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (u v : Fin 3 × Fin n) (hv : 0 < P v.1 v.2) :
    threeRowReducedGradient P u.1 u.2 ≤ threeRowReducedGradient P v.1 v.2 := by
  have h := hmax.gradient_le hP u v hv
  simp only [separationGradient_threeRow] at h
  linarith only [h]

theorem IsSeparationGlobalMax.threeRow_gradient_eq {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (u v : Fin 3 × Fin n) (hu : 0 < P u.1 u.2) (hv : 0 < P v.1 v.2) :
    threeRowReducedGradient P u.1 u.2 = threeRowReducedGradient P v.1 v.2 :=
  le_antisymm (hmax.threeRow_gradient_le hP u v hv) (hmax.threeRow_gradient_le hP v u hu)

theorem threeRowPair_nonneg {n : ℕ} {P : Board 3 n} (hP : ∀ i j, 0 ≤ P i j) (i : Fin 3) :
    0 ≤ threeRowPair P i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hP _ j) (hP _ j)

/-- The missing-row comparison keeps the derivative of the column triple product. -/
theorem threeRowReducedGradient_row_difference {n : ℕ} (P : Board 3 n) (i : Fin 3) (j : Fin n) :
    threeRowReducedGradient P i j - threeRowReducedGradient P (i + 1) j =
      threeRowPair P i - threeRowPair P (i + 1) +
      (rowSum P (i + 1) - rowSum P i) * P (i + 2) j +
      (rowSum P (i + 2) - 2 * P (i + 2) j) * (P (i + 1) j - P i j) := by
  fin_cases i <;> simp [threeRowReducedGradient] <;> ring

end DittertRybin
