import DR.Rectangular.OrderThreeLarge

/-! Refined row and column controls for the five-row infinite strip. -/

namespace DittertRybin
open scoped BigOperators

/-- Zero total sum improves every coordinate bound by the exact (d-1)/d factor. -/
theorem orderThree_zero_sum_coordinate_sq {d : ℕ} (hd : 0 < d) (a : Fin d → ℝ)
    (ha : (∑ i, a i) = 0) (i : Fin d) :
    a i ^ 2 ≤ ((d : ℝ) - 1) / d * (∑ j, a j ^ 2) := by
  let S := (Finset.univ : Finset (Fin d)).erase i
  have hsum : (∑ j ∈ S, a j) = -a i := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := a) (Finset.mem_univ i)
    rw [ha] at h
    change (∑ j ∈ S, a j) + a i = 0 at h
    linarith
  have hsq : (∑ j ∈ S, a j ^ 2) = (∑ j, a j ^ 2) - a i ^ 2 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := fun j => a j ^ 2) (Finset.mem_univ i)
    change (∑ j ∈ S, a j ^ 2) + a i ^ 2 = _ at h
    linarith
  have hcNat : S.card + 1 = d := by
    simpa only [S, Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_add_one (s := (Finset.univ : Finset (Fin d))) (Finset.mem_univ i)
  have hc : (S.card : ℝ) = (d : ℝ) - 1 := by
    have hcR : (S.card : ℝ) + 1 = d := by exact_mod_cast hcNat
    linarith
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S a (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  rw [hsum, hsq, hc] at hCS
  have hbound : a i ^ 2 * (d : ℝ) ≤ ((d : ℝ) - 1) * (∑ j, a j ^ 2) := by nlinarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    a i ^ 2 ≤ (((d : ℝ) - 1) * (∑ j, a j ^ 2)) / d := (le_div_iff₀ hdR).mpr hbound
    _ = _ := by ring

/-- Keep the improved row factor separate from the column bound. -/
theorem orderThree_linear_upper_refined {m n : ℕ} (hm : 0 < m)
    (X : Board m n) (hX : totalMass X = 0) :
    orderThreeLinearMoment X ≤
      (Real.sqrt ((((m : ℝ) - 1) / m) * orderThreeRowSquareSum X) +
        Real.sqrt (orderThreeColSquareSum X)) * orderThreeSquareSum X := by
  have hrow (i : Fin m) := Real.le_sqrt_of_sq_le
    (orderThree_zero_sum_coordinate_sq hm (rowSum X) hX i)
  have hcol (j : Fin n) := Real.le_sqrt_of_sq_le (orderThree_col_sq_le X j)
  unfold orderThreeLinearMoment orderThreeSquareSum
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [orderThreeRowSquareSum, mul_comm] using mul_le_mul_of_nonneg_left
    (add_le_add (hrow i) (hcol j)) (sq_nonneg (X i j))

/-- Discarding the nonnegative column projection permits its energy to be completed exactly. -/
theorem orderThree_mixed_lower_row_residual {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    -Real.sqrt ((orderThreeSquareSum X - orderThreeRowSquareSum X / n) * orderThreeRowSquareSum X) *
        Real.sqrt (orderThreeColSquareSum X) ≤ orderThreeMixedMoment X := by
  have hA := orderThreeRowSquareSum_nonneg X
  have hB := orderThreeColSquareSum_nonneg X
  have hT : orderThreeRowSquareSum X / n ≤ orderThreeMarginalSquareSum X :=
    le_add_of_nonneg_right (div_nonneg hB (Nat.cast_nonneg m))
  have hE := orderThreeMarginalSquareSum_le hm hn X hX
  have hres : 0 ≤ orderThreeSquareSum X - orderThreeRowSquareSum X / n :=
    sub_nonneg.mpr (hT.trans hE)
  have hC := orderThree_mixed_sq_le hm hn X hX
  have hup := mul_le_mul_of_nonneg_right (sub_le_sub_left hT (orderThreeSquareSum X))
    (mul_nonneg hA hB)
  have hh : orderThreeMixedMoment X ^ 2 ≤
      (Real.sqrt ((orderThreeSquareSum X - orderThreeRowSquareSum X / n) * orderThreeRowSquareSum X) *
        Real.sqrt (orderThreeColSquareSum X)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hres hA), Real.sq_sqrt hB]
    nlinarith
  have hp := (abs_le_of_sq_le_sq' hh (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
  simpa only [neg_mul] using hp

theorem orderThree_sqrt_completion (B D K : ℝ) (hB : 0 ≤ B) (hD : 0 < D) :
    -9 * K ^ 2 / D ≤ D * B - 6 * Real.sqrt B * K := by
  have h := orderThree_quadratic_completion K B 1 D (Real.sqrt B) (by norm_num) hD
    (by simpa using (Real.sq_sqrt hB).le)
  convert h using 1
  ring

end DittertRybin
