import DR.Rectangular.ThreeRowNoEmpty
import DR.Rectangular.OrderThreeSampling

namespace DittertRybin.Tests.ThreeRowNoEmpty
open scoped BigOperators

private theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
private theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
private theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
private theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
private theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
private theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

private def oneColumn : Board 1 3 := fun _ j => if j = 0 then 1 else 0
private noncomputable def firstSplit : Board 1 3 := blendColumns oneColumn 1 0 (1 / 2)
private noncomputable def secondSplit : Board 1 3 := blendColumns firstSplit 2 0 (1 / 2)

example : IsProbability oneColumn := by
  constructor
  · intro i j
    fin_cases j <;> norm_num [oneColumn]
  · norm_num [totalMass, rowSum, oneColumn, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

-- The first split is flat: there are still fewer than three occupied columns.
example : separationProbability oneColumn 3 = 0 := by
  rw [separationProbability_three_homogeneous]
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum, oneColumn, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

example : separationProbability firstSplit 3 = 0 := by
  rw [separationProbability_three_homogeneous]
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum, firstSplit,
    oneColumn, blendColumns, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

-- The second split has genuine positive gain; no first-step strictness was assumed.
example : separationProbability secondSplit 3 = 3 / 16 := by
  rw [separationProbability_three_homogeneous]
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum, secondSplit,
    firstSplit, oneColumn, blendColumns, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

example : totalMass (eraseColumns oneColumn {1, 0}) = 0 := by
  norm_num [totalMass, rowSum, eraseColumns, oneColumn, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

example : totalMass (eraseColumns firstSplit {2, 0}) = 1 / 2 := by
  norm_num [totalMass, rowSum, eraseColumns, firstSplit, oneColumn, blendColumns, Fin.sum_univ_succ, ne01, ne02, ne10, ne12, ne20, ne21]

example {n : ℕ} (hn : 3 ≤ n) {P : Board 3 n} (hP : IsProbability P)
    (hmax : IsSeparationGlobalMax P 3) :
    (∀ i, 0 < rowSum P i) ∧ (∀ j, 0 < colSum P j) :=
  ⟨hmax.row_mass_pos hP (by norm_num), hmax.column_mass_pos hP hn⟩

#print axioms DittertRybin.averagingKernel_one_quadratic_pos
#print axioms DittertRybin.IsSeparationGlobalMax.no_zero_column
#print axioms DittertRybin.IsSeparationGlobalMax.column_mass_pos
#print axioms DittertRybin.IsSeparationGlobalMax.row_mass_pos

end DittertRybin.Tests.ThreeRowNoEmpty
