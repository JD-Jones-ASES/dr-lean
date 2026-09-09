import DR.Collision.MomentBounds
import DR.Collision.Intersections
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.GCongr

/-!
# Concentration forced by collision bounds

The variance and marginal estimates concern the actual full probability
matrix. The first step is the elementary projection of cell variance onto
each row or column; no assumption about an interior support is used.
-/

open scoped BigOperators

namespace DittertRybin

/-- Dimension-normalized squared distance from the uniform board. -/
noncomputable def normalizedVariance {m n : ℕ} (P : Board m n) : ℝ :=
  (m : ℝ) * n * cellVariance P

theorem normalizedVariance_nonneg {m n : ℕ} (P : Board m n) :
    0 ≤ normalizedVariance P :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (cellVariance_nonneg P)

theorem rowSum_uniformBoard {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin m) :
    rowSum (uniformBoard m n) i = (m : ℝ)⁻¹ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [rowSum, uniformBoard, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem colSum_uniformBoard {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin n) :
    colSum (uniformBoard m n) j = (n : ℝ)⁻¹ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [colSum, uniformBoard, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

private theorem sum_sq_le_card_mul_sum_sq {d : ℕ} (x : Fin d → ℝ) :
    (∑ i, x i) ^ 2 ≤ (d : ℝ) * ∑ i, x i ^ 2 := by
  simpa [mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun _ => (1 : ℝ))

theorem row_deviation_sq_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (i : Fin m) :
    (rowSum P i - (m : ℝ)⁻¹) ^ 2 ≤ (n : ℝ) * cellVariance P := by
  have heq : rowSum P i - (m : ℝ)⁻¹ =
      ∑ j, (P i j - uniformBoard m n i j) := by
    rw [Finset.sum_sub_distrib, ← rowSum, ← rowSum, rowSum_uniformBoard hm hn]
  have hpart : (∑ j, (P i j - uniformBoard m n i j) ^ 2) ≤ cellVariance P := by
    unfold cellVariance
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum
      (fun u _ => Finset.sum_nonneg fun j _ =>
        sq_nonneg (P u j - uniformBoard m n u j)) (Finset.mem_univ i)
  rw [heq]
  exact (sum_sq_le_card_mul_sum_sq _).trans
    (mul_le_mul_of_nonneg_left hpart (Nat.cast_nonneg n))

theorem col_deviation_sq_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (j : Fin n) :
    (colSum P j - (n : ℝ)⁻¹) ^ 2 ≤ (m : ℝ) * cellVariance P := by
  have heq : colSum P j - (n : ℝ)⁻¹ =
      ∑ i, (P i j - uniformBoard m n i j) := by
    rw [Finset.sum_sub_distrib, ← colSum, ← colSum, colSum_uniformBoard hm hn]
  have hpart : (∑ i, (P i j - uniformBoard m n i j) ^ 2) ≤ cellVariance P := by
    unfold cellVariance
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.single_le_sum
      (fun v _ => Finset.sum_nonneg fun i _ =>
        sq_nonneg (P i v - uniformBoard m n i v)) (Finset.mem_univ j)
  rw [heq]
  exact (sum_sq_le_card_mul_sum_sq _).trans
    (mul_le_mul_of_nonneg_left hpart (Nat.cast_nonneg m))

theorem rowSum_le_of_variance {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (i : Fin m) :
    rowSum P i ≤ (m : ℝ)⁻¹ + Real.sqrt (normalizedVariance P / m) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have heq : normalizedVariance P / m = (n : ℝ) * cellVariance P := by
    unfold normalizedVariance
    field_simp
  have h := Real.le_sqrt_of_sq_le (row_deviation_sq_le hm hn P i)
  rw [heq]
  linarith

theorem colSum_le_of_variance {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) (j : Fin n) :
    colSum P j ≤ (n : ℝ)⁻¹ + Real.sqrt (normalizedVariance P / n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have heq : normalizedVariance P / n = (m : ℝ) * cellVariance P := by
    unfold normalizedVariance
    field_simp
  have h := Real.le_sqrt_of_sq_le (col_deviation_sq_le hm hn P j)
  rw [heq]
  linarith

/-- The largest row or column marginal, for positive matrix dimensions. -/
noncomputable def peakMarginal {m n : ℕ} (P : Board m n) : ℝ :=
  max (⨆ i, rowSum P i) (⨆ j, colSum P j)

theorem rowSum_le_peakMarginal {m n : ℕ} (P : Board m n) (i : Fin m) :
    rowSum P i ≤ peakMarginal P := by
  exact (le_ciSup (Set.finite_range (rowSum P)).bddAbove i).trans (le_max_left _ _)

theorem colSum_le_peakMarginal {m n : ℕ} (P : Board m n) (j : Fin n) :
    colSum P j ≤ peakMarginal P := by
  exact (le_ciSup (Set.finite_range (colSum P)).bddAbove j).trans (le_max_right _ _)

theorem peakMarginal_nonneg {m n : ℕ} (hm : 0 < m) {P : Board m n}
    (hP : IsProbability P) : 0 ≤ peakMarginal P :=
  (rowSum_nonneg hP.1 ⟨0, hm⟩).trans (rowSum_le_peakMarginal P ⟨0, hm⟩)

theorem peakMarginal_le_of_variance {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Board m n) :
    peakMarginal P ≤ ((min m n : ℕ) : ℝ)⁻¹ +
      Real.sqrt (normalizedVariance P / (min m n : ℕ)) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd : (0 : ℝ) < (min m n : ℕ) := Nat.cast_pos.mpr (lt_min hm hn)
  have hdm : ((min m n : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr (min_le_left _ _)
  have hdn : ((min m n : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr (min_le_right _ _)
  have hz := normalizedVariance_nonneg P
  apply max_le
  · apply ciSup_le
    intro i
    apply (rowSum_le_of_variance hm hn P i).trans
    gcongr
  · apply ciSup_le
    intro j
    apply (colSum_le_of_variance hm hn P j).trans
    gcongr

/-- Every contender's cell variance is controlled by its largest marginal. -/
theorem contender_variance_le_collision {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k)
    (hcont : separationProbability (uniformBoard m n) k ≤ separationProbability P k) :
    normalizedVariance P ≤ (collisionConstant k : ℝ) * peakMarginal P := by
  let A : ℝ := k.choose 2
  let C : ℝ := ((k.choose 2) ^ 2).choose 2
  let u : ℝ := (m : ℝ) * n
  have hA : 0 < A := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hu : 0 < u := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
  have hη := peakMarginal_nonneg hm hP
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hq : 1 - separationProbability P k ≤ A ^ 2 / u :=
    (sub_le_sub_left hcont 1).trans (failure_uniform_le hm hn)
  have hlower := collisionFirstSum_lower hm hn hP hk
  have hupper := collisionFirstSum_le_failure (k := k) hP (peakMarginal P) hη
    (rowSum_le_peakMarginal P) (colSum_le_peakMarginal P)
  have hcombine : A ^ 2 / u + A * cellVariance P ≤
      (1 + C * peakMarginal P) * (A ^ 2 / u) := by
    calc
      _ ≤ collisionFirstSum P k := by simpa only [div_eq_mul_inv] using hlower
      _ ≤ (1 + C * peakMarginal P) * (1 - separationProbability P k) := hupper
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hcombine hu.le
  have hclear : A ^ 2 + A * cellVariance P * u ≤
      (1 + C * peakMarginal P) * A ^ 2 := by
    field_simp at hscaled
    nlinarith [hscaled]
  have hcancel : A * (u * cellVariance P) ≤ A * (C * A * peakMarginal P) := by
    nlinarith [hclear]
  have hfinal := (mul_le_mul_iff_right₀ hA).mp hcancel
  simpa only [normalizedVariance, collisionConstant, Nat.cast_mul, A, C, u, mul_comm,
    mul_left_comm, mul_assoc] using hfinal

/-- Actual-matrix concentration of every contender, with no stationary or support assumptions. -/
theorem contender_concentration {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k)
    (hcont : separationProbability (uniformBoard m n) k ≤ separationProbability P k) :
    normalizedVariance P < ((collisionConstant k : ℝ) + 1) ^ 2 / (min m n : ℕ) ∧
      peakMarginal P < ((collisionConstant k : ℝ) + 2) / (min m n : ℕ) := by
  apply FiniteEvents.concentration_bootstrap
  · exact Nat.cast_pos.mpr (lt_min hm hn)
  · exact Nat.cast_nonneg _
  · exact normalizedVariance_nonneg P
  · exact contender_variance_le_collision hm hn hP hk hcont
  · simpa only [one_div] using peakMarginal_le_of_variance hm hn P

end DittertRybin
