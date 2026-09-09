import DR.Square.Stationarity
import DR.Square.CapacityUnivariate

/-!
# Marginals and the shared deficit of a square contender

Every nonnegative mass-n matrix whose objective is at least the uniform
value has positive marginals. The row and column product deficits share
the permanent deficit budget; they are not bounded independently and then
added. No permanent lower bound or Dittert maximization claim is assumed.
-/

namespace DittertRybin

open scoped BigOperators

theorem dittertConstant_lt_one {n : ℕ} (hn : 2 ≤ n) : dittertConstant n < 1 := by
  have hfac : n.factorial < n ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    calc
      (k + 1).factorial ≤ (k + 1) * k ^ k := Nat.mul_le_mul_left _ k.factorial_le_pow
      _ < (k + 1) * (k + 1) ^ k := by
        apply Nat.mul_lt_mul_of_pos_left _ (by omega)
        exact Nat.pow_lt_pow_left (by omega) (by omega)
      _ = (k + 1) ^ (k + 1) := by rw [pow_succ']
  have hpow : (0 : ℝ) < (n : ℝ) ^ n := pow_pos (by exact_mod_cast (show 0 < n by omega)) _
  rw [dittertConstant, div_lt_one hpow]
  exact_mod_cast hfac

theorem rowProduct_le_one {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n) : (∏ i, rowSum A i) ≤ 1 := by
  have h := prod_le_arithMean_pow hn (rowSum A) (rowSum_nonneg hA)
  change (∏ i, rowSum A i) ≤ (totalMass A / n) ^ n at h
  simpa [hmass, Nat.cast_ne_zero.mpr hn.ne'] using h

theorem colProduct_le_one {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n) : (∏ j, colSum A j) ≤ 1 := by
  have h := prod_le_arithMean_pow hn (colSum A) (colSum_nonneg hA)
  rw [← totalMass_eq_sum_colSum, hmass] at h
  simpa [Nat.cast_ne_zero.mpr hn.ne'] using h

/-- The exact joint deficit budget at any contender, including zero permanent. -/
theorem dittert_contender_deficit_budget {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) :
    0 ≤ 1 - (∏ i, rowSum A i) ∧ 0 ≤ 1 - (∏ j, colSum A j) ∧
      (1 - (∏ i, rowSum A i)) + (1 - (∏ j, colSum A j)) ≤ dittertConstant n - A.permanent ∧
      0 ≤ dittertConstant n - A.permanent ∧ dittertConstant n - A.permanent ≤ dittertConstant n := by
  have hR := rowProduct_le_one (by omega) A hA hmass
  have hC := colProduct_le_one (by omega) A hA hmass
  have hp := permanent_nonneg hA
  unfold dittertFunctional at hcont
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Contenders have positive row and column products even on a proper support face. -/
theorem dittert_contender_products_pos {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) :
    0 < (∏ i, rowSum A i) ∧ 0 < (∏ j, colSum A j) := by
  have hR := rowProduct_le_one (by omega) A hA hmass
  have hC := colProduct_le_one (by omega) A hA hmass
  have hp := permanent_nonneg hA
  have hg := dittertConstant_lt_one hn
  unfold dittertFunctional at hcont
  constructor <;> linarith

/-- Marginal positivity needed for stationarity is a consequence, not a support assumption. -/
theorem dittert_contender_marginals_pos {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) :
    (∀ i, 0 < rowSum A i) ∧ (∀ j, 0 < colSum A j) := by
  obtain ⟨hR, hC⟩ := dittert_contender_products_pos hn A hA hmass hcont
  constructor
  · intro i
    have hne := Finset.prod_ne_zero_iff.mp hR.ne' i (Finset.mem_univ i)
    exact lt_of_le_of_ne (rowSum_nonneg hA i) hne.symm
  · intro j
    have hne := Finset.prod_ne_zero_iff.mp hC.ne' j (Finset.mem_univ j)
    exact lt_of_le_of_ne (colSum_nonneg hA j) hne.symm

theorem uniformDittertMatrix_rowSum {n : ℕ} (hn : 0 < n) (i : Fin n) :
    rowSum (uniformDittertMatrix n) i = 1 := by
  simp [rowSum, uniformDittertMatrix, Nat.cast_ne_zero.mpr hn.ne']

theorem uniformDittertMatrix_colSum {n : ℕ} (hn : 0 < n) (j : Fin n) :
    colSum (uniformDittertMatrix n) j = 1 := by
  simp [colSum, uniformDittertMatrix, Nat.cast_ne_zero.mpr hn.ne']

theorem uniformDittertMatrix_totalMass {n : ℕ} (hn : 0 < n) :
    totalMass (uniformDittertMatrix n) = n := by
  simp [totalMass, uniformDittertMatrix_rowSum hn]

theorem dittertFunctional_uniform {n : ℕ} (hn : 0 < n) :
    dittertFunctional (uniformDittertMatrix n) = 2 - dittertConstant n := by
  have hp : (uniformDittertMatrix n).permanent = dittertConstant n := permanent_uniform_square n
  norm_num [dittertFunctional, uniformDittertMatrix_rowSum hn, uniformDittertMatrix_colSum hn, hp]

/-- Every attained global maximum is a contender by comparison to the feasible uniform matrix. -/
theorem dittert_globalMax_isContender {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) :
    2 - dittertConstant n ≤ dittertFunctional A := by
  rw [← dittertFunctional_uniform hn]
  exact hmax _ (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    (uniformDittertMatrix_totalMass hn)

/-- Both coefficients in the stationary pair are positive at every square contender. -/
theorem dittert_contender_stationary_coefficients_pos {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) :
    0 < ((∏ r, rowSum A r) - A.permanent) / (∏ j, colSum A j) ∧
      0 < ((∏ j, colSum A j) - A.permanent) / (∏ r, rowSum A r) := by
  obtain ⟨hRpos, hCpos⟩ := dittert_contender_products_pos hn A hA hmass hcont
  have hR := rowProduct_le_one (by omega) A hA hmass
  have hC := colProduct_le_one (by omega) A hA hmass
  have hg := dittertConstant_lt_one hn
  unfold dittertFunctional at hcont
  exact ⟨div_pos (by linarith) hCpos, div_pos (by linarith) hRpos⟩

/-- The full stationary pair has no marginal-positivity or support restriction in its hypotheses. -/
theorem dittert_globalMax_stationary_pair {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) :
    (∀ i, (((∏ r, rowSum A r) - A.permanent) / (∏ j, colSum A j)) * (rowSum A i - 1) =
      -(∑ j, A i j * (colSum A j - 1) / colSum A j)) ∧
    (∀ j, (((∏ c, colSum A c) - A.permanent) / (∏ i, rowSum A i)) * (colSum A j - 1) =
      -(∑ i, A i j * (rowSum A i - 1) / rowSum A i)) := by
  have hn0 : 0 < n := by omega
  have hcont := dittert_globalMax_isContender hn0 A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  exact ⟨dittert_globalMax_row_deviation hn0 A hA hmass hr hc hmax,
    dittert_globalMax_col_deviation hn0 A hA hmass hr hc hmax⟩

end DittertRybin
