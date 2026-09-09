import DR.Square.Contenders
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The normalized matrix in the stationary spectral argument

Nonnegative cell masses with positive marginals define a contraction between
the two Euclidean coordinate spaces. Zero cells are allowed. All norm bounds
below are finite sums of squares, so no abstract spectral theorem is needed.
-/

namespace DittertRybin

open scoped BigOperators

noncomputable def normalizedBipartiteMatrix {m n : ℕ} (A : Board m n) : Board m n :=
  fun i j => A i j / (Real.sqrt (rowSum A i) * Real.sqrt (colSum A j))

noncomputable def normalizedRowDeviation {m n : ℕ} (A : Board m n) (i : Fin m) : ℝ :=
  (rowSum A i - 1) / Real.sqrt (rowSum A i)

noncomputable def normalizedColDeviation {m n : ℕ} (A : Board m n) (j : Fin n) : ℝ :=
  (colSum A j - 1) / Real.sqrt (colSum A j)

/-- Finite weighted Cauchy--Schwarz, including zero weights. -/
theorem weighted_sum_mul_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i) * ∑ i, a i * b i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i) * b i)
  have hmul (i : ι) : Real.sqrt (a i) * (Real.sqrt (a i) * b i) = a i * b i := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (ha i)]
  simpa only [hmul, mul_pow, Real.sq_sqrt (ha _)] using hcs

theorem normalizedBipartiteMatrix_apply_sum {m n : ℕ} (A : Board m n) (z : Fin n → ℝ)
    (i : Fin m) :
    (∑ j, normalizedBipartiteMatrix A i j * z j) =
      (∑ j, A i j * (z j / Real.sqrt (colSum A j))) / Real.sqrt (rowSum A i) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [normalizedBipartiteMatrix, div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalizedBipartiteMatrix_row_contraction {m n : ℕ} (A : Board m n)
    (hA : ∀ i j, 0 ≤ A i j) (hr : ∀ i, 0 < rowSum A i) (z : Fin n → ℝ) (i : Fin m) :
    (∑ j, normalizedBipartiteMatrix A i j * z j) ^ 2 ≤
      ∑ j, A i j * (z j / Real.sqrt (colSum A j)) ^ 2 := by
  have h := weighted_sum_mul_sq_le (A i) (fun j => z j / Real.sqrt (colSum A j)) (hA i)
  rw [normalizedBipartiteMatrix_apply_sum, div_pow, Real.sq_sqrt (hr i).le]
  apply (div_le_iff₀ (hr i)).mpr
  simpa only [rowSum, mul_comm] using h

/-- The normalized nonnegative rectangular matrix is an exact Euclidean contraction. -/
theorem normalizedBipartiteMatrix_contraction {m n : ℕ} (A : Board m n)
    (hA : ∀ i j, 0 ≤ A i j) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (z : Fin n → ℝ) :
    (∑ i, (∑ j, normalizedBipartiteMatrix A i j * z j) ^ 2) ≤ ∑ j, z j ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ j, A i j * (z j / Real.sqrt (colSum A j)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => normalizedBipartiteMatrix_row_contraction A hA hr z i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← colSum, div_pow, Real.sq_sqrt (hc j).le]
      field_simp [(hc j).ne']

/-- The positive column marginal vector maps to the row marginal vector. -/
theorem normalizedBipartiteMatrix_sqrt_col {m n : ℕ} (A : Board m n)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j) (i : Fin m) :
    (∑ j, normalizedBipartiteMatrix A i j * Real.sqrt (colSum A j)) = Real.sqrt (rowSum A i) := by
  rw [normalizedBipartiteMatrix_apply_sum]
  simp only [div_self (Real.sqrt_pos.mpr (hc _)).ne', mul_one]
  rw [← rowSum]
  have hs : Real.sqrt (rowSum A i) ^ 2 = rowSum A i := Real.sq_sqrt (hr i).le
  apply (div_eq_iff (Real.sqrt_pos.mpr (hr i)).ne').mpr
  nlinarith

theorem normalizedBipartiteMatrix_transpose {m n : ℕ} (A : Board m n) :
    normalizedBipartiteMatrix A.transpose = (normalizedBipartiteMatrix A).transpose := by
  ext i j
  simp [normalizedBipartiteMatrix, rowSum, colSum, Matrix.transpose_apply, mul_comm]

theorem normalizedBipartiteMatrix_colDeviation {m n : ℕ} (A : Board m n)
    (hc : ∀ j, 0 < colSum A j) (i : Fin m) :
    (∑ j, normalizedBipartiteMatrix A i j * normalizedColDeviation A j) =
      (∑ j, A i j * (colSum A j - 1) / colSum A j) / Real.sqrt (rowSum A i) := by
  rw [normalizedBipartiteMatrix_apply_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [normalizedColDeviation, div_div, ← pow_two, Real.sq_sqrt (hc j).le]
  ring

/-- The first exact singular-vector equation at an arbitrary global Dittert maximum. -/
theorem dittert_globalMax_normalized_row {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (i : Fin n) :
    (∑ j, normalizedBipartiteMatrix A i j * normalizedColDeviation A j) =
      -(((∏ r, rowSum A r) - A.permanent) / (∏ j, colSum A j)) * normalizedRowDeviation A i := by
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  obtain ⟨hrow, _⟩ := dittert_globalMax_stationary_pair hn A hA hmass hmax
  rw [normalizedBipartiteMatrix_colDeviation A hc]
  have h := hrow i
  have hnum : (∑ j, A i j * (colSum A j - 1) / colSum A j) =
      -(((∏ r, rowSum A r) - A.permanent) / (∏ j, colSum A j)) * (rowSum A i - 1) := by
    linarith
  rw [hnum, normalizedRowDeviation]
  ring

/-- The transpose singular-vector equation has the exact second stationary coefficient. -/
theorem dittert_globalMax_normalized_col {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (j : Fin n) :
    (∑ i, normalizedBipartiteMatrix A i j * normalizedRowDeviation A i) =
      -(((∏ c, colSum A c) - A.permanent) / (∏ i, rowSum A i)) * normalizedColDeviation A j := by
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  obtain ⟨_, hcol⟩ := dittert_globalMax_stationary_pair hn A hA hmass hmax
  have hid := normalizedBipartiteMatrix_colDeviation A.transpose hr j
  rw [normalizedBipartiteMatrix_transpose] at hid
  change (∑ i, normalizedBipartiteMatrix A i j * normalizedRowDeviation A i) =
    (∑ i, A i j * (rowSum A i - 1) / rowSum A i) / Real.sqrt (colSum A j) at hid
  rw [hid]
  have h := hcol j
  have hnum : (∑ i, A i j * (rowSum A i - 1) / rowSum A i) =
      -(((∏ c, colSum A c) - A.permanent) / (∏ i, rowSum A i)) * (colSum A j - 1) := by
    linarith
  rw [hnum, normalizedColDeviation]
  ring

theorem normalizedRowDeviation_weighted_sum {n : ℕ} (A : Board n n)
    (hr : ∀ i, 0 < rowSum A i) (hmass : totalMass A = n) :
    (∑ i, Real.sqrt (rowSum A i) * normalizedRowDeviation A i) = 0 := by
  have hterm (i : Fin n) : Real.sqrt (rowSum A i) * normalizedRowDeviation A i = rowSum A i - 1 := by
    dsimp [normalizedRowDeviation]
    field_simp [(Real.sqrt_pos.mpr (hr i)).ne']
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  change totalMass A - _ = 0
  simp [hmass]

theorem normalizedColDeviation_weighted_sum {n : ℕ} (A : Board n n)
    (hc : ∀ j, 0 < colSum A j) (hmass : totalMass A = n) :
    (∑ j, Real.sqrt (colSum A j) * normalizedColDeviation A j) = 0 := by
  have hmassT : totalMass A.transpose = n := by
    change (∑ j, colSum A j) = n
    rw [← totalMass_eq_sum_colSum, hmass]
  exact normalizedRowDeviation_weighted_sum A.transpose hc hmassT

end DittertRybin
