import DR.Rectangular.FourRowCorrection
import Mathlib.Analysis.Real.Sqrt

/-!
# The actual four-row leading gauge

The cubic `g_i` is formed from the other three row masses. Its elementary
bound gives a positive real square root even at boundary row distributions.
The corresponding column gauge keeps every zero cell and zero column.
-/

namespace DittertRybin

open scoped BigOperators

noncomputable def fourRowGaugeCollision (r : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, r j ^ 2 * r k

noncomputable def fourRowGaugeWeight (r : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  Real.sqrt (1 - fourRowGaugeCollision r i)

noncomputable def fourRowGaugeColumn {n : ℕ} (P : Board 4 n) (j : Fin n) : ℝ :=
  ∑ i, fourRowGaugeWeight (rowSum P) i * P i j

/-- The sharp elementary cubic bound used for the column-to-gauge comparison. -/
theorem fourRowGaugeCollision_bounds (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (i : Fin 4) :
    0 ≤ fourRowGaugeCollision r i ∧ fourRowGaugeCollision r i ≤ 1 / 4 := by
  have hg0 : 0 ≤ fourRowGaugeCollision r i :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (hr k)
  let S := Finset.univ.erase i
  let b := ∑ j ∈ S, r j
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun j _ => hr j
  have hb1 : b ≤ 1 := by
    calc
      b ≤ ∑ j, r j := Finset.sum_le_univ_sum_of_nonneg hr
      _ = 1 := hsum
  have hother (j : Fin 4) (hj : j ∈ S) : (∑ k ∈ S.erase j, r k) = b - r j := by
    have h := Finset.sum_erase_add S r hj
    change (∑ k ∈ S.erase j, r k) + r j = b at h
    linarith
  have hterm (j : Fin 4) (hj : j ∈ S) :
      (∑ k ∈ S.erase j, r j ^ 2 * r k) ≤ r j * (b ^ 2 / 4) := by
    rw [← Finset.mul_sum, hother j hj]
    have hquad : r j * (b - r j) ≤ b ^ 2 / 4 := by nlinarith [sq_nonneg (r j - b/2)]
    have h := mul_le_mul_of_nonneg_left hquad (hr j)
    nlinarith
  have hsumg : fourRowGaugeCollision r i ≤ b ^ 3 / 4 := by
    calc
      _ ≤ ∑ j ∈ S, r j * (b ^ 2 / 4) := Finset.sum_le_sum hterm
      _ = b ^ 3 / 4 := by rw [← Finset.sum_mul]; change b * (b^2/4) = _; ring
  have hb3 : b ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hb0 hb1 3
  exact ⟨hg0, by linarith⟩

theorem fourRowGaugeWeight_bounds (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (i : Fin 4) :
    Real.sqrt (3 / 4) ≤ fourRowGaugeWeight r i ∧ fourRowGaugeWeight r i ≤ 1 := by
  obtain ⟨h0,h1⟩ := fourRowGaugeCollision_bounds r hr hsum i
  constructor
  · apply Real.sqrt_le_sqrt
    linarith
  · change Real.sqrt (1 - fourRowGaugeCollision r i) ≤ 1
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by linarith⟩

/-- The column gauges are nonnegative, dominated by column masses, and control their squares. -/
theorem fourRowGaugeColumn_bounds {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (j : Fin n) : 0 ≤ fourRowGaugeColumn P j ∧
      fourRowGaugeColumn P j ≤ colSum P j ∧
      colSum P j ^ 2 ≤ (4 / 3) * fourRowGaugeColumn P j ^ 2 := by
  have hw (i : Fin 4) := fourRowGaugeWeight_bounds (rowSum P) (rowSum_nonneg hP.1) hP.2 i
  have ha0 : 0 ≤ fourRowGaugeColumn P j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (hP.1 i j)
  have haupper : fourRowGaugeColumn P j ≤ colSum P j := by
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_right (hw i).2 (hP.1 i j)).trans_eq (one_mul _)
  have hlower : Real.sqrt (3 / 4) * colSum P j ≤ fourRowGaugeColumn P j := by
    simp only [colSum, Finset.mul_sum, fourRowGaugeColumn]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i).1 (hP.1 i j)
  have hsquare := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg (3/4))
    (colSum_nonneg hP.1 j)) hlower 2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/4)] at hsquare
  exact ⟨ha0, haupper, by nlinarith⟩

/-- Summing actual column gauges leaves the row-marginal scalar gauge. -/
theorem fourRowGaugeColumn_sum {n : ℕ} (P : Board 4 n) :
    (∑ j, fourRowGaugeColumn P j) = ∑ i, rowSum P i * fourRowGaugeWeight (rowSum P) i := by
  simp only [fourRowGaugeColumn]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  simp only [rowSum, mul_comm]

/-- The rational coefficient 17 safely absorbs the actual cubic column remainder. -/
theorem fourRowGaugeColumn_cube {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (j : Fin n) : 11 * colSum P j ^ 3 ≤ 17 * fourRowGaugeColumn P j ^ 3 := by
  obtain ⟨ha0, _, hsquare⟩ := fourRowGaugeColumn_bounds P hP j
  have hcap : colSum P j ≤ (52 / 45) * fourRowGaugeColumn P j := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [sq_nonneg (fourRowGaugeColumn P j)]
  have hcube := pow_le_pow_left₀ (colSum_nonneg hP.1 j) hcap 3
  have ha3 : 0 ≤ fourRowGaugeColumn P j ^ 3 := pow_nonneg ha0 _
  nlinarith

theorem fourRowGaugeColumn_sum_le_one {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    (∑ j, fourRowGaugeColumn P j) ≤ 1 := by
  calc
    _ ≤ ∑ j, colSum P j := Finset.sum_le_sum fun j _ => (fourRowGaugeColumn_bounds P hP j).2.1
    _ = 1 := (totalMass_eq_sum_colSum P).symm.trans hP.2

end DittertRybin
