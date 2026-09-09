import DR.Rectangular.ThreeRowComparison

namespace DittertRybin.Tests
open scoped BigOperators

private def missingCellBoard : Board 3 1 := fun i _ => if i = 0 then 0 else if i = 1 then 2 else 3

private theorem n01 : (0 : Fin 3) ≠ 1 := by decide
private theorem n02 : (0 : Fin 3) ≠ 2 := by decide
private theorem n10 : (1 : Fin 3) ≠ 0 := by decide
private theorem n12 : (1 : Fin 3) ≠ 2 := by decide
private theorem n20 : (2 : Fin 3) ≠ 0 := by decide
private theorem n21 : (2 : Fin 3) ≠ 1 := by decide

-- The missing cell still has a nonzero actual derivative.
example : separationGradient missingCellBoard 3 0 0 = 36 := by
  rw [separationGradient_threeRow]
  norm_num [threeRowReducedGradient, threeRowPair, totalMass, rowSum, colSum,
    missingCellBoard, Fin.sum_univ_succ, Fin.add_def, n01, n02, n10, n12, n20, n21]

-- Omitting the derivative of the column triple product would give this false value.
example : ¬ separationGradient missingCellBoard 3 0 0 = 108 := by
  rw [separationGradient_threeRow]
  norm_num [threeRowReducedGradient, threeRowPair, totalMass, rowSum, colSum,
    missingCellBoard, Fin.sum_univ_succ, Fin.add_def, n01, n02, n10, n12, n20, n21]

-- Signed perturbations are covered by the exact polynomial identity.
example (t : ℝ) : separationProbability (threeRowAddCell missingCellBoard 0 0 t) 3 = 36 * t := by
  rw [separationProbability_threeRow_addCell, separationProbability_threeRow_cubic]
  norm_num [threeRowSuccessPolynomial, threeRowReducedGradient, threeRowPair, totalMass,
    rowSum, colSum, missingCellBoard, Fin.sum_univ_succ, Fin.add_def, n01, n02, n10, n12, n20, n21]

example {n : ℕ} (P : Board 3 n) (a b : Fin n) (i : Fin 3) :
    threeRowReducedGradient P i a - threeRowReducedGradient P i b =
      -(∑ h, threeRowColumnComparison P a b i h * (P h a - P h b)) :=
  threeRow_column_gradient_difference P a b i

-- The target cell is allowed to be zero; the donor alone is required positive.
example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (a b : Fin n) (i : Fin 3) (hib : 0 < P i b) :
    0 ≤ ∑ h, threeRowColumnComparison P a b i h * (P h a - P h b) :=
  hmax.threeRow_comparison_nonneg hP a b i hib

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b) : 0 < totalMass P - colSum P a - colSum P b :=
  hmax.threeRow_remaining_mass_pos hP hn a b hab

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (i : Fin 3) (j : Fin n) (hp : 0 < P i j) (h1 : P (i + 1) j = 0)
    (h2 : P (i + 2) j = 0) : 0 < threeRowPair P i :=
  hmax.threeRow_singleton_pair_pos hP i j hp h1 h2

#print axioms separationProbability_threeRow_cubic
#print axioms separationGradient_threeRow
#print axioms threeRow_column_gradient_difference
#print axioms IsSeparationGlobalMax.threeRow_singleton_pair_pos
end DittertRybin.Tests
