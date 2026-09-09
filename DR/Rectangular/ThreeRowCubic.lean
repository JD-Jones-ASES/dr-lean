import DR.Rectangular.OrderThreeSampling
import DR.Rectangular.ThreeRowKKT

/-!
# The actual three-row cubic on an arbitrary number of columns

The formula is homogeneous and valid for signed boards. Keeping the column
triple term is essential when later differentiating at a missing cell.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def threeRowPair {n : ℕ} (P : Board 3 n) (i : Fin 3) : ℝ :=
  ∑ j, P (i + 1) j * P (i + 2) j

/-- Six times the three-row rook polynomial, written without any divisions. -/
noncomputable def threeRowSuccessPolynomial {n : ℕ} (P : Board 3 n) : ℝ :=
  totalMass P ^ 3 + ∑ j,
    (-3 * totalMass P * colSum P j ^ 2 + 2 * colSum P j ^ 3 +
      6 * (∑ i, rowSum P i * P (i + 1) j * P (i + 2) j) -
      12 * P 0 j * P 1 j * P 2 j)

/-- The column-dependent part of the derivative divided by six.
The omitted term is common to every cell and cancels in all KKT comparisons. -/
noncomputable def threeRowReducedGradient {n : ℕ} (P : Board 3 n) (i : Fin 3) (j : Fin n) : ℝ :=
  -colSum P j * (totalMass P - colSum P j) + threeRowPair P i +
    rowSum P (i + 1) * P (i + 2) j + rowSum P (i + 2) * P (i + 1) j -
      2 * P (i + 1) j * P (i + 2) j

/-- A local column identity, with the row masses still those of the full physical board. -/
theorem threeRow_column_cubic {n : ℕ} (P : Board 3 n) (j : Fin n) :
    -3 * totalMass P * colSum P j ^ 2 + 2 * colSum P j ^ 3 +
      6 * (∑ i, rowSum P i * P (i + 1) j * P (i + 2) j) -
      12 * P 0 j * P 1 j * P 2 j =
    -(3 * totalMass P * (∑ i, P i j ^ 2) +
      6 * (∑ i, P i j * rowSum P i * colSum P j) -
      6 * (∑ i, P i j ^ 2 * (rowSum P i + colSum P j)) + 4 * ∑ i, P i j ^ 3) := by
  simp [totalMass, colSum, Fin.sum_univ_succ]
  ring

/-- Reindexing the actual failure polynomial by physical columns. -/
theorem threeRowFailurePolynomial_by_columns {n : ℕ} (P : Board 3 n) :
    orderThreeFailurePolynomial P = ∑ j,
      (3 * totalMass P * (∑ i, P i j ^ 2) +
      6 * (∑ i, P i j * rowSum P i * colSum P j) -
      6 * (∑ i, P i j ^ 2 * (rowSum P i + colSum P j)) + 4 * ∑ i, P i j ^ 3) := by
  unfold orderThreeFailurePolynomial
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : (∑ i, ∑ j, P i j ^ 2) = ∑ j, ∑ i, P i j ^ 2 := Finset.sum_comm
  have hm : (∑ i, ∑ j, P i j * rowSum P i * colSum P j) =
      ∑ j, ∑ i, P i j * rowSum P i * colSum P j := Finset.sum_comm
  have hl : (∑ i, ∑ j, P i j ^ 2 * (rowSum P i + colSum P j)) =
      ∑ j, ∑ i, P i j ^ 2 * (rowSum P i + colSum P j) := Finset.sum_comm
  have h3 : (∑ i, ∑ j, P i j ^ 3) = ∑ j, ∑ i, P i j ^ 3 := Finset.sum_comm
  rw [h2, hm, hl, h3]

/-- This is the genuine iid inclusive-OR probability, for every signed three-row board. -/
theorem separationProbability_threeRow_cubic {n : ℕ} (P : Board 3 n) :
    separationProbability P 3 = threeRowSuccessPolynomial P := by
  rw [separationProbability_three_homogeneous, threeRowFailurePolynomial_by_columns]
  unfold threeRowSuccessPolynomial
  simp_rw [threeRow_column_cubic]
  rw [Finset.sum_neg_distrib]
  ring

theorem threeRowSuccessPolynomial_grouped {n : ℕ} (P : Board 3 n) :
    threeRowSuccessPolynomial P = totalMass P ^ 3 -
      3 * totalMass P * (∑ j, colSum P j ^ 2) + 2 * (∑ j, colSum P j ^ 3) +
      6 * (∑ i, rowSum P i * threeRowPair P i) - 12 * ∑ j, P 0 j * P 1 j * P 2 j := by
  unfold threeRowSuccessPolynomial threeRowPair
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hp : (∑ j, ∑ i, rowSum P i * P (i + 1) j * P (i + 2) j) =
      ∑ i, rowSum P i * ∑ j, P (i + 1) j * P (i + 2) j := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_assoc]
  have ht : (∑ j, 12 * P 0 j * P 1 j * P 2 j) = 12 * ∑ j, P 0 j * P 1 j * P 2 j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hp, ht]
  ring

end DittertRybin
