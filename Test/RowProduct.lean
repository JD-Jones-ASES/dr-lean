import DR.Endpoint.RowProduct

namespace DittertRybin.Tests
open scoped BigOperators

private def weightedDiagonal : Board 2 2 := Matrix.diagonal ![(2 : ℝ),3]

-- Each original row has its own law: different row masses disappear separately.
example : rowAvoidance (normalizeRows weightedDiagonal) = 1 := by
  rw [rowAvoidance_normalizeRows, rowAvoidance_square_eq_permanent]
  norm_num [weightedDiagonal, Matrix.permanent_diagonal, rowSum, Matrix.diagonal_apply,
    Fin.prod_univ_two, Fin.sum_univ_succ]

-- A single row assignment has no permutation multiplicity.
example : rookSum weightedDiagonal 2 = 6 := by
  rw [rookSum_endpoint_eq_rowAvoidance, rowAvoidance_square_eq_permanent]
  norm_num [weightedDiagonal, Matrix.permanent_diagonal, Fin.prod_univ_two]

-- Ordered iid cell samples have the separate factorial factor.
example : eventMass (fun a : Fin 2 × Fin 2 => weightedDiagonal a.1 a.2)
    {s : Fin 2 → Fin 2 × Fin 2 | RowsDistinct s ∧ ColsDistinct s} = 12 := by
  rw [eventMass_endpoint_rows_cols]
  norm_num [weightedDiagonal, Matrix.permanent_diagonal, Fin.prod_univ_two]

-- Signed weights are allowed in the polynomial identity, before probability claims.
example : rowAvoidance (Matrix.diagonal ![(-2 : ℝ),3]) = -6 := by
  rw [rowAvoidance_square_eq_permanent]
  norm_num [Matrix.permanent_diagonal, Fin.prod_univ_two]

-- A zero row must not acquire probability mass through division by zero.
example : rowSum (normalizeRows (0 : Board 2 3)) 0 = 0 := by
  simp [rowSum, normalizeRows]

example : ¬ rowSum (normalizeRows (0 : Board 2 3)) 0 = 1 := by
  simp [rowSum, normalizeRows]

-- Empty row assignments carry weight one, consistent with the empty permanent.
example : rowAvoidance (0 : Board 0 0) = 1 := by
  rw [rowAvoidance_square_eq_permanent]
  simp [Matrix.permanent]

#print axioms rowAssignmentEvent_compl
#print axioms rowAvoidance_le_one
#print axioms rookSum_endpoint_normalized
#print axioms rowAvoidance_square_eq_permanent
end DittertRybin.Tests
