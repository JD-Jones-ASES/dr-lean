import DR.Rectangular.OrderThreePolynomial
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite norm estimates for the three-sample rectangular theorem

The estimates apply to actual real matrices, including zero entries. The
orthogonal residual removes row and column means from a zero-mass matrix.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def orderThreeSquareSum {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ i, ∑ j, X i j ^ 2

noncomputable def orderThreeRowSquareSum {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ i, rowSum X i ^ 2

noncomputable def orderThreeColSquareSum {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ j, colSum X j ^ 2

noncomputable def orderThreeMarginalSquareSum {m n : ℕ} (X : Board m n) : ℝ :=
  orderThreeRowSquareSum X / n + orderThreeColSquareSum X / m

noncomputable def orderThreeResidual {m n : ℕ} (X : Board m n) : Board m n :=
  fun i j => X i j - rowSum X i / n - colSum X j / m

theorem orderThreeSquareSum_nonneg {m n : ℕ} (X : Board m n) :
    0 ≤ orderThreeSquareSum X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (X i j)

theorem orderThreeRowSquareSum_nonneg {m n : ℕ} (X : Board m n) :
    0 ≤ orderThreeRowSquareSum X := Finset.sum_nonneg fun i _ => sq_nonneg (rowSum X i)

theorem orderThreeColSquareSum_nonneg {m n : ℕ} (X : Board m n) :
    0 ≤ orderThreeColSquareSum X := Finset.sum_nonneg fun j _ => sq_nonneg (colSum X j)

theorem orderThreeMarginalSquareSum_nonneg {m n : ℕ} (X : Board m n) :
    0 ≤ orderThreeMarginalSquareSum X :=
  add_nonneg (div_nonneg (orderThreeRowSquareSum_nonneg X) (Nat.cast_nonneg _))
    (div_nonneg (orderThreeColSquareSum_nonneg X) (Nat.cast_nonneg _))

theorem orderThree_entry_sq_le {m n : ℕ} (X : Board m n) (i : Fin m) (j : Fin n) :
    X i j ^ 2 ≤ orderThreeSquareSum X := by
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (X i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (X k l))
      (Finset.mem_univ i))

theorem orderThree_row_sq_le {m n : ℕ} (X : Board m n) (i : Fin m) :
    rowSum X i ^ 2 ≤ orderThreeRowSquareSum X :=
  Finset.single_le_sum (fun k _ => sq_nonneg (rowSum X k)) (Finset.mem_univ i)

theorem orderThree_col_sq_le {m n : ℕ} (X : Board m n) (j : Fin n) :
    colSum X j ^ 2 ≤ orderThreeColSquareSum X :=
  Finset.single_le_sum (fun k _ => sq_nonneg (colSum X k)) (Finset.mem_univ j)

theorem orderThreeSquareSum_eq_zero_iff {m n : ℕ} (X : Board m n) :
    orderThreeSquareSum X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext i j
    have hi := orderThree_entry_sq_le X i j
    rw [h] at hi
    exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
  · rintro rfl
    simp [orderThreeSquareSum]

/-- A lower entry bound controls the signed cubic sum, without positivity of the deviations. -/
theorem orderThree_cube_lower {m n : ℕ} (X : Board m n) (h : ℝ)
    (hX : ∀ i j, -h ≤ X i j) :
    -h * orderThreeSquareSum X ≤ ∑ i, ∑ j, X i j ^ 3 := by
  simp only [orderThreeSquareSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_nonneg (sq_nonneg (X i j)) (by linarith [hX i j] : 0 ≤ X i j + h)]

/-- The third moment is bounded by the three-halves power of the second moment. -/
theorem orderThree_cube_upper {m n : ℕ} (P : Board m n) :
    (∑ i, ∑ j, P i j ^ 3) ≤ orderThreeSquareSum P * Real.sqrt (orderThreeSquareSum P) := by
  rw [orderThreeSquareSum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hi := Real.le_sqrt_of_sq_le (orderThree_entry_sq_le P i j)
  have hm := mul_le_mul_of_nonneg_left hi (sq_nonneg (P i j))
  simpa only [orderThreeSquareSum, pow_succ] using hm

/-- Every probability cell lies in the closed unit interval. -/
theorem orderThree_probability_entry_le_one {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (i : Fin m) (j : Fin n) : P i j ≤ 1 := by
  have hi : P i j ≤ rowSum P i := Finset.single_le_sum (fun k _ => hP.1 i k) (Finset.mem_univ j)
  have hr : rowSum P i ≤ totalMass P :=
    Finset.single_le_sum (fun k _ => rowSum_nonneg hP.1 k) (Finset.mem_univ i)
  exact (hi.trans hr).trans_eq hP.2

theorem orderThree_probability_squareSum_le_one {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) : orderThreeSquareSum P ≤ 1 := by
  calc
    orderThreeSquareSum P ≤ ∑ i, ∑ j, P i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [hP.1 i j, orderThree_probability_entry_le_one hP i j]
    _ = 1 := hP.2

theorem orderThree_sum_mul_row {m n : ℕ} (X : Board m n) (f : Fin m → ℝ) :
    (∑ i, ∑ j, X i j * f i) = ∑ i, rowSum X i * f i := by
  simp only [← Finset.sum_mul, rowSum]

theorem orderThree_sum_mul_col {m n : ℕ} (X : Board m n) (f : Fin n → ℝ) :
    (∑ i, ∑ j, X i j * f j) = ∑ j, colSum X j * f j := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, colSum]

theorem orderThreeResidual_rowSum {m n : ℕ} (hn : 0 < n) (X : Board m n)
    (hX : totalMass X = 0) (i : Fin m) : rowSum (orderThreeResidual X) i = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [orderThreeResidual, rowSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
  change rowSum X i - n * (rowSum X i / n) - (∑ j, colSum X j) / m = 0
  rw [← totalMass_eq_sum_colSum, hX]
  field_simp
  ring

theorem orderThreeResidual_colSum {m n : ℕ} (hm : 0 < m) (X : Board m n)
    (hX : totalMass X = 0) (j : Fin n) : colSum (orderThreeResidual X) j = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simp only [orderThreeResidual, colSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
  change colSum X j - (∑ i, rowSum X i) / n - m * (colSum X j / m) = 0
  change colSum X j - totalMass X / n - m * (colSum X j / m) = 0
  rw [hX]
  field_simp
  ring

/-- Exact orthogonal decomposition into the row, column, and residual directions. -/
theorem orderThree_energy_decomposition {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    orderThreeSquareSum X = orderThreeSquareSum (orderThreeResidual X) +
      orderThreeMarginalSquareSum X := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hr : (∑ i, ∑ _j : Fin n, (rowSum X i / n) ^ 2) = orderThreeRowSquareSum X / n := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      div_pow, ← Finset.mul_sum, ← Finset.sum_div, orderThreeRowSquareSum]
    field_simp
  have hc : (∑ _i : Fin m, ∑ j, (colSum X j / m) ^ 2) = orderThreeColSquareSum X / m := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      div_pow, ← Finset.sum_div, orderThreeColSquareSum]
    field_simp
  have hzr : (∑ i, ∑ j, orderThreeResidual X i j * (rowSum X i / n)) = 0 := by
    rw [orderThree_sum_mul_row]
    simp only [orderThreeResidual_rowSum hn X hX, zero_mul, Finset.sum_const_zero]
  have hzc : (∑ i, ∑ j, orderThreeResidual X i j * (colSum X j / m)) = 0 := by
    rw [orderThree_sum_mul_col]
    simp only [orderThreeResidual_colSum hm X hX, zero_mul, Finset.sum_const_zero]
  have hrc : (∑ i, ∑ j, (rowSum X i / n) * (colSum X j / m)) = 0 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
    change (totalMass X / n) * ((∑ j, colSum X j) / m) = 0
    rw [hX, zero_div, zero_mul]
  have hp (i : Fin m) (j : Fin n) :
      X i j ^ 2 = orderThreeResidual X i j ^ 2 + (rowSum X i / n) ^ 2 +
        (colSum X j / m) ^ 2 + 2 * (orderThreeResidual X i j * (rowSum X i / n)) +
        2 * (orderThreeResidual X i j * (colSum X j / m)) +
        2 * ((rowSum X i / n) * (colSum X j / m)) := by
    dsimp [orderThreeResidual]
    ring
  unfold orderThreeSquareSum
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hr, hc, hzr, hzc]
  simp only [← Finset.mul_sum] at hrc
  rw [hrc]
  unfold orderThreeMarginalSquareSum
  ring

theorem orderThreeMarginalSquareSum_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    orderThreeMarginalSquareSum X ≤ orderThreeSquareSum X := by
  rw [orderThree_energy_decomposition hm hn X hX]
  exact le_add_of_nonneg_left (orderThreeSquareSum_nonneg _)

noncomputable def orderThreeMixedMoment {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ i, ∑ j, X i j * rowSum X i * colSum X j

noncomputable def orderThreeLinearMoment {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ i, ∑ j, X i j ^ 2 * (rowSum X i + colSum X j)

theorem orderThree_mixed_residual {m n : ℕ} (X : Board m n)
    (hX : totalMass X = 0) :
    orderThreeMixedMoment X = ∑ i, ∑ j,
      orderThreeResidual X i j * rowSum X i * colSum X j := by
  have hp (i : Fin m) (j : Fin n) :
      orderThreeResidual X i j * rowSum X i * colSum X j =
        X i j * rowSum X i * colSum X j -
        (rowSum X i ^ 2 / n) * colSum X j - rowSum X i * (colSum X j ^ 2 / m) := by
    dsimp [orderThreeResidual]
    ring
  simp_rw [hp, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  change orderThreeMixedMoment X = orderThreeMixedMoment X -
    (∑ i, rowSum X i ^ 2 / n) * (∑ j, colSum X j) -
    totalMass X * (∑ j, colSum X j ^ 2 / m)
  rw [← totalMass_eq_sum_colSum, hX]
  ring

/-- Cauchy--Schwarz uses only the orthogonal residual in the mixed cubic term. -/
theorem orderThree_mixed_sq_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    orderThreeMixedMoment X ^ 2 ≤
      (orderThreeSquareSum X - orderThreeMarginalSquareSum X) *
        orderThreeRowSquareSum X * orderThreeColSquareSum X := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a : Fin m × Fin n => orderThreeResidual X a.1 a.2)
    (fun a : Fin m × Fin n => rowSum X a.1 * colSum X a.2)
  simp only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul] at h
  have hz : orderThreeSquareSum (orderThreeResidual X) =
      orderThreeSquareSum X - orderThreeMarginalSquareSum X := by
    linarith [orderThree_energy_decomposition hm hn X hX]
  calc
    orderThreeMixedMoment X ^ 2 ≤ orderThreeSquareSum (orderThreeResidual X) *
        orderThreeRowSquareSum X * orderThreeColSquareSum X := by
      rw [orderThree_mixed_residual X hX]
      simpa only [orderThreeSquareSum, orderThreeRowSquareSum, orderThreeColSquareSum,
        mul_assoc] using h
    _ = _ := by rw [hz]

/-- Arithmetic--geometric mean in the two marginal energies. -/
theorem orderThree_marginal_product_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) :
    4 * orderThreeRowSquareSum X * orderThreeColSquareSum X ≤
      (m : ℝ) * n * orderThreeMarginalSquareSum X ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have heq : (m : ℝ) * n * orderThreeMarginalSquareSum X ^ 2 -
      4 * orderThreeRowSquareSum X * orderThreeColSquareSum X =
      ((m : ℝ) * orderThreeRowSquareSum X - n * orderThreeColSquareSum X) ^ 2 /
        ((m : ℝ) * n) := by
    unfold orderThreeMarginalSquareSum
    field_simp
    ring
  have hh := div_nonneg (sq_nonneg ((m : ℝ) * orderThreeRowSquareSum X -
    n * orderThreeColSquareSum X)) (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
  linarith

theorem orderThree_row_col_le_sqrt {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (i : Fin m) (j : Fin n) :
    rowSum X i + colSum X j ≤
      Real.sqrt (((m : ℝ) + n) * orderThreeMarginalSquareSum X) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : (rowSum X i + colSum X j) ^ 2 ≤
      ((m : ℝ) + n) * (rowSum X i ^ 2 / n + colSum X j ^ 2 / m) := by
    have heq : ((m : ℝ) + n) * (rowSum X i ^ 2 / n + colSum X j ^ 2 / m) -
        (rowSum X i + colSum X j) ^ 2 =
        ((m : ℝ) * rowSum X i - n * colSum X j) ^ 2 / ((m : ℝ) * n) := by
      field_simp
      ring
    have hh := div_nonneg (sq_nonneg ((m : ℝ) * rowSum X i - n * colSum X j))
      (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
    linarith
  have hp : rowSum X i ^ 2 / n + colSum X j ^ 2 / m ≤ orderThreeMarginalSquareSum X :=
    add_le_add (div_le_div_of_nonneg_right (orderThree_row_sq_le X i) (Nat.cast_nonneg n))
      (div_le_div_of_nonneg_right (orderThree_col_sq_le X j) (Nat.cast_nonneg m))
  exact Real.le_sqrt_of_sq_le (hs.trans (mul_le_mul_of_nonneg_left hp
    (add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))))

theorem orderThree_linear_upper {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) :
    orderThreeLinearMoment X ≤
      Real.sqrt (((m : ℝ) + n) * orderThreeMarginalSquareSum X) * orderThreeSquareSum X := by
  unfold orderThreeLinearMoment orderThreeSquareSum
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (orderThree_row_col_le_sqrt hm hn X i j) (sq_nonneg (X i j))

end DittertRybin
