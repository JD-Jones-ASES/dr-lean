import DR.Rectangular.OrderThreeLargeBounds
import DR.Collision.Concentration

/-! Exact centered expansion of the actual three-sample failure polynomial. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def orderThreeTranslate {m n : ℕ} (X : Board m n) (t : ℝ) : Board m n :=
  fun i j => X i j + t

theorem orderThreeTranslate_rowSum {m n : ℕ} (X : Board m n) (t : ℝ) (i : Fin m) :
    rowSum (orderThreeTranslate X t) i = rowSum X i + n * t := by
  simp [rowSum, orderThreeTranslate, Finset.sum_add_distrib]

theorem orderThreeTranslate_colSum {m n : ℕ} (X : Board m n) (t : ℝ) (j : Fin n) :
    colSum (orderThreeTranslate X t) j = colSum X j + m * t := by
  simp [colSum, orderThreeTranslate, Finset.sum_add_distrib]

theorem orderThreeTranslate_totalMass {m n : ℕ} (X : Board m n) (t : ℝ) :
    totalMass (orderThreeTranslate X t) = totalMass X + m * n * t := by
  simp only [totalMass, orderThreeTranslate_rowSum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem orderThreeTranslate_squareSum {m n : ℕ} (X : Board m n) (t : ℝ)
    (hX : totalMass X = 0) :
    orderThreeSquareSum (orderThreeTranslate X t) = orderThreeSquareSum X + m * n * t ^ 2 := by
  have hs : (∑ i, ∑ j, X i j) = 0 := hX
  simp only [orderThreeSquareSum, orderThreeTranslate, add_sq, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hs]
  ring

theorem orderThreeTranslate_cubeSum {m n : ℕ} (X : Board m n) (t : ℝ)
    (hX : totalMass X = 0) :
    (∑ i, ∑ j, orderThreeTranslate X t i j ^ 3) =
      (∑ i, ∑ j, X i j ^ 3) + 3 * t * orderThreeSquareSum X + m * n * t ^ 3 := by
  have hs : (∑ i, ∑ j, X i j) = 0 := hX
  have hp (i : Fin m) (j : Fin n) : orderThreeTranslate X t i j ^ 3 =
      X i j ^ 3 + 3 * t * X i j ^ 2 + 3 * t ^ 2 * X i j + t ^ 3 := by
    dsimp [orderThreeTranslate]
    ring
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs, orderThreeSquareSum]
  ring

theorem orderThree_sum_cell_row {m n : ℕ} (X : Board m n) :
    (∑ i, ∑ j, X i j * rowSum X i) = orderThreeRowSquareSum X := by
  rw [orderThree_sum_mul_row]
  simp only [orderThreeRowSquareSum, pow_two]

theorem orderThree_sum_cell_col {m n : ℕ} (X : Board m n) :
    (∑ i, ∑ j, X i j * colSum X j) = orderThreeColSquareSum X := by
  rw [orderThree_sum_mul_col]
  simp only [orderThreeColSquareSum, pow_two]

theorem orderThree_sum_row_over_cells {m n : ℕ} (X : Board m n)
    (hX : totalMass X = 0) : (∑ i, ∑ _j : Fin n, rowSum X i) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  change n * totalMass X = 0
  rw [hX, mul_zero]

theorem orderThree_sum_col_over_cells {m n : ℕ} (X : Board m n)
    (hX : totalMass X = 0) : (∑ _i : Fin m, ∑ j, colSum X j) = 0 := by
  rw [← totalMass_eq_sum_colSum, hX]
  simp

theorem orderThree_sum_row_col {m n : ℕ} (X : Board m n)
    (hX : totalMass X = 0) : (∑ i, ∑ j, rowSum X i * colSum X j) = 0 := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  change totalMass X * (∑ j, colSum X j) = 0
  rw [hX, zero_mul]

theorem orderThreeTranslate_mixedMoment {m n : ℕ} (X : Board m n) (t : ℝ)
    (hX : totalMass X = 0) :
    orderThreeMixedMoment (orderThreeTranslate X t) = orderThreeMixedMoment X +
      m * t * orderThreeRowSquareSum X + n * t * orderThreeColSquareSum X +
      m ^ 2 * n ^ 2 * t ^ 3 := by
  have hs : (∑ i, ∑ j, X i j) = 0 := hX
  have hp (i : Fin m) (j : Fin n) :
      orderThreeTranslate X t i j * rowSum (orderThreeTranslate X t) i *
        colSum (orderThreeTranslate X t) j =
      X i j * rowSum X i * colSum X j +
      (m * t) * (X i j * rowSum X i) + (n * t) * (X i j * colSum X j) +
      (m * n * t ^ 2) * X i j + t * (rowSum X i * colSum X j) +
      (m * t ^ 2) * rowSum X i + (n * t ^ 2) * colSum X j + m * n * t ^ 3 := by
    rw [orderThreeTranslate_rowSum, orderThreeTranslate_colSum]
    dsimp [orderThreeTranslate]
    ring
  unfold orderThreeMixedMoment
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [orderThree_sum_cell_row, orderThree_sum_cell_col, hs,
    orderThree_sum_row_over_cells X hX, orderThree_sum_col_over_cells X hX]
  have hrc := orderThree_sum_row_col X hX
  simp only [← Finset.mul_sum] at hrc
  rw [hrc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem orderThreeTranslate_linearMoment {m n : ℕ} (X : Board m n) (t : ℝ)
    (hX : totalMass X = 0) :
    orderThreeLinearMoment (orderThreeTranslate X t) = orderThreeLinearMoment X +
      2 * t * orderThreeRowSquareSum X + 2 * t * orderThreeColSquareSum X +
      (m + n) * t * orderThreeSquareSum X + m * n * (m + n) * t ^ 3 := by
  have hs : (∑ i, ∑ j, X i j) = 0 := hX
  have hp (i : Fin m) (j : Fin n) :
      orderThreeTranslate X t i j ^ 2 * (rowSum (orderThreeTranslate X t) i +
        colSum (orderThreeTranslate X t) j) =
      X i j ^ 2 * (rowSum X i + colSum X j) + 2 * t * (X i j * rowSum X i) +
      2 * t * (X i j * colSum X j) + t ^ 2 * rowSum X i + t ^ 2 * colSum X j +
      (m + n) * t * X i j ^ 2 + 2 * (m + n) * t ^ 2 * X i j + (m + n) * t ^ 3 := by
    rw [orderThreeTranslate_rowSum, orderThreeTranslate_colSum]
    dsimp [orderThreeTranslate]
    ring
  unfold orderThreeLinearMoment
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [orderThree_sum_cell_row, orderThree_sum_cell_col, hs,
    orderThree_sum_row_over_cells X hX, orderThree_sum_col_over_cells X hX]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    orderThreeSquareSum]
  ring

theorem orderThreeFailurePolynomial_constant (m n : ℕ) (t : ℝ) :
    orderThreeFailurePolynomial (fun (_i : Fin m) (_j : Fin n) => t) =
      (9 * m * n - 6 * m - 6 * n + 4) * m * n * t ^ 3 := by
  simp only [orderThreeFailurePolynomial, totalMass, rowSum, colSum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Exact homogeneous translation formula around a constant board. -/
theorem orderThreeFailurePolynomial_translate {m n : ℕ} (X : Board m n) (t : ℝ)
    (hX : totalMass X = 0) :
    orderThreeFailurePolynomial (orderThreeTranslate X t) -
      orderThreeFailurePolynomial (fun (_i : Fin m) (_j : Fin n) => t) =
      3 * t * (m - 2) * (n - 2) * orderThreeSquareSum X +
      6 * t * (m - 2) * orderThreeRowSquareSum X +
      6 * t * (n - 2) * orderThreeColSquareSum X +
      4 * (∑ i, ∑ j, X i j ^ 3) + 6 * orderThreeMixedMoment X - 6 * orderThreeLinearMoment X := by
  change 3 * totalMass (orderThreeTranslate X t) * orderThreeSquareSum (orderThreeTranslate X t) +
    6 * orderThreeMixedMoment (orderThreeTranslate X t) -
    6 * orderThreeLinearMoment (orderThreeTranslate X t) +
    4 * (∑ i, ∑ j, orderThreeTranslate X t i j ^ 3) - _ = _
  rw [orderThreeTranslate_totalMass, hX, orderThreeTranslate_squareSum X t hX,
    orderThreeTranslate_mixedMoment X t hX, orderThreeTranslate_linearMoment X t hX,
    orderThreeTranslate_cubeSum X t hX, orderThreeFailurePolynomial_constant]
  ring

noncomputable def orderThreeCentered {m n : ℕ} (P : Board m n) : Board m n :=
  fun i j => P i j - uniformBoard m n i j

theorem orderThreeCentered_totalMass {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) : totalMass (orderThreeCentered P) = 0 := by
  have hU := uniformBoard_isProbability hm hn
  simp only [totalMass, rowSum, orderThreeCentered, Finset.sum_sub_distrib]
  change totalMass P - totalMass (uniformBoard m n) = 0
  rw [hP.2, hU.2, sub_self]

theorem orderThreeCentered_translate {m n : ℕ} (P : Board m n) :
    orderThreeTranslate (orderThreeCentered P) ((m : ℝ) * n)⁻¹ = P := by
  ext i j
  simp only [orderThreeTranslate, orderThreeCentered, uniformBoard, sub_add_cancel]

theorem orderThreeCentered_eq_zero_iff {m n : ℕ} (P : Board m n) :
    orderThreeCentered P = 0 ↔ P = uniformBoard m n := by
  constructor
  · intro h
    ext i j
    have hi := congrFun (congrFun h i) j
    exact sub_eq_zero.mp hi
  · rintro rfl
    ext i j
    exact sub_self _

theorem orderThreeCentered_squareSum {m n : ℕ} (P : Board m n) :
    orderThreeSquareSum (orderThreeCentered P) = cellVariance P := by
  simp only [cellVariance, Fintype.sum_prod_type, orderThreeSquareSum, orderThreeCentered]

theorem orderThreeFailurePolynomial_uniform {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    orderThreeFailurePolynomial (uniformBoard m n) =
      9 * ((m : ℝ) * n)⁻¹ - 6 * ((m : ℝ) * n)⁻¹ * ((m : ℝ)⁻¹ + (n : ℝ)⁻¹) +
      4 * (((m : ℝ) * n)⁻¹) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold uniformBoard
  rw [orderThreeFailurePolynomial_constant]
  field_simp
  ring

/-- The complete cubic expansion, including all boundary points of the simplex. -/
theorem orderThreeFailurePolynomial_centered {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) =
      3 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * ((n : ℝ) - 2) *
        orderThreeSquareSum (orderThreeCentered P) +
      6 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * orderThreeRowSquareSum (orderThreeCentered P) +
      6 * (((m : ℝ) * n)⁻¹) * ((n : ℝ) - 2) * orderThreeColSquareSum (orderThreeCentered P) +
      4 * (∑ i, ∑ j, orderThreeCentered P i j ^ 3) +
      6 * orderThreeMixedMoment (orderThreeCentered P) - 6 * orderThreeLinearMoment (orderThreeCentered P) := by
  have h := orderThreeFailurePolynomial_translate (orderThreeCentered P) (((m : ℝ) * n)⁻¹)
    (orderThreeCentered_totalMass hm hn hP)
  unfold uniformBoard
  simpa only [orderThreeCentered_translate] using h

end DittertRybin
