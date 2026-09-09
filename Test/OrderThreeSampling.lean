import DR.Rectangular.OrderThreeSampling

/-! Exact repeated-cell, L-shape, and signed-mass sampling controls. -/

open scoped BigOperators
open DittertRybin

private noncomputable def lShape : Board 2 2 := ![![1/3, 1/3], ![1/3, 0]]

example : orderThreeFailurePolynomial lShape = 1 := by
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum, lShape, Fin.sum_univ_two]

/-- The three nonzero cells still have at most two row and column labels. -/
example : separationProbability lShape 3 = 0 := by
  rw [separationProbability_three_homogeneous]
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum, lShape, Fin.sum_univ_two]

/-- Repeated-cell failure alone misses the six ordered L configurations. -/
example : 3 * (∑ i, ∑ j, lShape i j ^ 2) - 2 * (∑ i, ∑ j, lShape i j ^ 3) = 7/9 := by
  norm_num [lShape, Fin.sum_univ_two]

example : orderThreeFailurePolynomial (fun _ _ => (2 : ℝ) : Board 1 1) = 8 := by
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum]

example : eventMass (fun _ : Fin 1 × Fin 1 => (-1 : ℝ))
    {s : Fin 3 → Fin 1 × Fin 1 | ¬ (RowsDistinct s ∨ ColsDistinct s)} = -1 := by
  have h := eventMass_failure_three (fun _ _ => (-1 : ℝ) : Board 1 1)
  norm_num [orderThreeFailurePolynomial, totalMass, rowSum, colSum] at h
  simpa only [not_or] using h

example {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsProbability P) :
    1 - separationProbability P 3 =
      3 * (∑ i, ∑ j, P i j ^ 2) + 6 * (∑ i, ∑ j, P i j * rowSum P i * colSum P j) -
      6 * (∑ i, ∑ j, P i j ^ 2 * (rowSum P i + colSum P j)) + 4 * (∑ i, ∑ j, P i j ^ 3) := by
  rw [one_sub_separationProbability_three hP, orderThreeFailurePolynomial, hP.2]
  ring

#print axioms DittertRybin.eventMass_failure_three
#print axioms DittertRybin.one_sub_separationProbability_three
