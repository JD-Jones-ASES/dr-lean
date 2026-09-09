import DR.Entropy
import DR.Semimatching
import DR.Collision.FirstMoment
import DR.Rectangular.OrderTwo
import Mathlib.Tactic.Ring

/-!
# Lower bound for the mixed collision moment

The middle term of the first collision sum is at least `1 / (m * n)`.
This follows from the two marginal entropy bounds and weighted Jensen,
with every zero entry and zero marginal retained in the domain.
-/

open scoped BigOperators

namespace DittertRybin

theorem entry_le_rowSum {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (i : Fin m) (j : Fin n) : P i j ≤ rowSum P i := by
  exact Finset.single_le_sum (fun j _ => hP i j) (Finset.mem_univ j)

theorem entry_le_colSum {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (i : Fin m) (j : Fin n) : P i j ≤ colSum P j := by
  exact Finset.single_le_sum (fun i _ => hP i j) (Finset.mem_univ i)

/-- Row-column logarithms separate exactly when averaged with joint weights. -/
theorem sum_weighted_log_marginals {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) :
    (∑ i, ∑ j, P i j * Real.log (rowSum P i * colSum P j)) =
      (∑ i, rowSum P i * Real.log (rowSum P i)) +
      ∑ j, colSum P j * Real.log (colSum P j) := by
  have hentry (i : Fin m) (j : Fin n) :
      P i j * Real.log (rowSum P i * colSum P j) =
      P i j * Real.log (rowSum P i) + P i j * Real.log (colSum P j) := by
    rcases eq_or_lt_of_le (hP i j) with hij | hij
    · simp [← hij]
    · rw [Real.log_mul (ne_of_gt (hij.trans_le (entry_le_rowSum hP i j)))
        (ne_of_gt (hij.trans_le (entry_le_colSum hP i j))), mul_add]
  simp_rw [hentry, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_mul _ _ _).symm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.sum_mul _ _ _).symm

/-- The universal lower bound for the overlapping-witness moment. -/
theorem mixed_collision_moment_lower {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    ((m : ℝ) * n)⁻¹ ≤ ∑ i, ∑ j, P i j * rowSum P i * colSum P j := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr := neg_log_card_le_sum_mul_log hm (rowSum P) (rowSum_nonneg hP.1) hP.2
  have hcs : ∑ j, colSum P j = 1 := (totalMass_eq_sum_colSum P).symm.trans hP.2
  have hc := neg_log_card_le_sum_mul_log hn (colSum P) (colSum_nonneg hP.1) hcs
  have hj := exp_sum_mul_log_le_sum_mul
    (fun a : Fin m × Fin n => P a.1 a.2)
    (fun a : Fin m × Fin n => rowSum P a.1 * colSum P a.2)
    (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2)
    (fun a ha => mul_pos (ha.trans_le (entry_le_rowSum hP.1 a.1 a.2))
      (ha.trans_le (entry_le_colSum hP.1 a.1 a.2)))
  simp only [Fintype.sum_prod_type] at hj
  rw [sum_weighted_log_marginals hP.1] at hj
  calc
    _ = Real.exp (-Real.log m - Real.log n) := by
      rw [← Real.exp_log (inv_pos.mpr (mul_pos hm0 hn0)), Real.log_inv,
        Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)]
      congr 1
      ring
    _ ≤ Real.exp ((∑ i, rowSum P i * Real.log (rowSum P i)) +
          ∑ j, colSum P j * Real.log (colSum P j)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ ≤ ∑ i, ∑ j, P i j * (rowSum P i * colSum P j) := hj
    _ = _ := by simp_rw [mul_assoc]

/-- A unit-sum real vector has second moment at least the uniform value. -/
theorem sum_squares_lower_of_sum_one {d : ℕ} (hd : 0 < d)
    (p : Fin d → ℝ) (hs : ∑ i, p i = 1) : (d : ℝ)⁻¹ ≤ ∑ i, p i ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hnonneg : 0 ≤ ∑ i, (p i - (d : ℝ)⁻¹) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hid : (∑ i, (p i - (d : ℝ)⁻¹) ^ 2) = (∑ i, p i ^ 2) - (d : ℝ)⁻¹ := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  linarith

/-- The disjoint-witness moment is no smaller than at uniform. -/
theorem product_marginal_squares_lower {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    ((m : ℝ) * n)⁻¹ ≤ rowSquareSum P * colSquareSum P := by
  have hr := sum_squares_lower_of_sum_one hm (rowSum P) hP.2
  have hc := sum_squares_lower_of_sum_one hn (colSum P)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2)
  rw [mul_inv]
  exact mul_le_mul hr hc (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Exact cell variance above the uniform second moment. -/
noncomputable def cellVariance {m n : ℕ} (P : Board m n) : ℝ :=
  ∑ a : Fin m × Fin n, (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2

theorem cellVariance_nonneg {m n : ℕ} (P : Board m n) : 0 ≤ cellVariance P :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cellSquareSum_eq_uniform_add_variance {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P : Board m n} (hP : IsProbability P) :
    cellSquareSum P = ((m : ℝ) * n)⁻¹ + cellVariance P := by
  have h := sum_sq_sub_uniformBoard hm hn hP
  change cellVariance P = _ at h
  change cellVariance P = cellSquareSum P - _ at h
  linarith

/-- The first collision sum exceeds its uniform value by the exact cell-variance term. -/
theorem collisionFirstSum_lower {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k) :
    (k.choose 2 : ℝ) ^ 2 * ((m : ℝ) * n)⁻¹ + (k.choose 2 : ℝ) * cellVariance P ≤
      collisionFirstSum P k := by
  have hmixed : ((m : ℝ) * n)⁻¹ ≤ mixedCollisionMoment P := by
    simpa only [mixedCollisionMoment, Fintype.sum_prod_type] using
      mixed_collision_moment_lower hm hn hP
  have hproduct := product_marginal_squares_lower hm hn hP
  have h3 := mul_le_mul_of_nonneg_left hmixed
    (show (0 : ℝ) ≤ 6 * k.choose 3 by positivity)
  have h4 := mul_le_mul_of_nonneg_left hproduct
    (show (0 : ℝ) ≤ 6 * k.choose 4 by positivity)
  have hcountN := collision_pattern_count_partition k
  rw [card_disjointWitness hk] at hcountN
  have hcount : (k.choose 2 : ℝ) ^ 2 =
      (k.choose 2 : ℝ) + 6 * k.choose 3 + 6 * k.choose 4 := by
    exact_mod_cast (by omega : (k.choose 2) ^ 2 = k.choose 2 + 6 * k.choose 3 + 6 * k.choose 4)
  rw [collisionFirstSum_formula hP hk, cellSquareSum_eq_uniform_add_variance hm hn hP,
    hcount]
  nlinarith

end DittertRybin
