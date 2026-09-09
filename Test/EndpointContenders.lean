import DR.Endpoint.LargeRowCaps
import DR.Endpoint.DeletedLaw
import Mathlib.Tactic.FinCases

namespace DittertRybin.Test
open scoped BigOperators

-- Exact rectangular probability normalization on arbitrary real boards.
example (P : Board 3 5) : separationProbability P 3 =
    (2/9:ℝ)*endpointRowProduct P+(12/25:ℝ)*endpointColumnRatio P-
      (2/9:ℝ)*endpointRookRatio P := by
  have h := separationProbability_endpoint_ratios (by norm_num : 0 < 3) (by norm_num : 3 ≤ 5) P
  norm_num [dittertConstant,distinctUniformProbability,Nat.descFactorial] at h
  exact h

-- The original row law at uniformity is b, rather than the iid joint-event probability a*b.
example : originalRowAvoidance (uniformBoard 3 5) = (12/25:ℝ) := by
  rw [originalRowAvoidance_uniform (by norm_num) (by norm_num)]
  norm_num [distinctUniformProbability,Nat.descFactorial]
example : originalRowAvoidance (uniformBoard 3 5) ≠ (2/9:ℝ)*(12/25) := by
  rw [originalRowAvoidance_uniform (by norm_num) (by norm_num)]
  norm_num [distinctUniformProbability,Nat.descFactorial]

-- Original row positivity is a conclusion on the whole nonnegative simplex.
example {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) (P : Board m n)
    (hP : IsProbability P) (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    (∀ i, 0 < ∑ j, P i j) ∧
      1-distinctUniformProbability n m ≤
        (∏ i, (m:ℝ)*(∑ j, P i j))*(1-rowAvoidance (normalizeRows P)) := by
  refine ⟨endpoint_contender_rows_pos hm hmn hP hcont,?_⟩
  simpa only [endpointRowProduct_eq_product,originalRowAvoidance,rowSum] using
    endpoint_contender_original_collision_relation hm hmn hP hcont

-- Uniform equality supplies a real contender at the smallest rectangular endpoint.
example : 1-distinctUniformProbability 3 2 ≤
    endpointRowProduct (uniformBoard 2 3)*(1-originalRowAvoidance (uniformBoard 2 3)) := by
  exact endpoint_contender_original_collision_relation (by norm_num) (by norm_num)
    (uniformBoard_isProbability (by norm_num) (by norm_num))
    (by rw [separationProbability_uniform (by norm_num) (by norm_num)])

-- Signed scaling and zero row sums remain valid in the polynomial row-law normalization.
example (P : Board 2 3) : normalizeRows ((-2:ℝ) • P) = normalizeRows P :=
  normalizeRows_smul P (by norm_num)

private def unequalDiagonal : Board 3 3 := Matrix.diagonal ![(2:ℝ),3,4]
private theorem deleted_diagonal : keepColumns unequalDiagonal ({(0:Fin 3),1}ᶜ) =
    Matrix.diagonal ![(0:ℝ),0,4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [keepColumns,unequalDiagonal,Matrix.diagonal_apply]

-- Positive retained mass does not ensure positive retained rows or an unchanged avoidance law.
example : totalMass (keepColumns unequalDiagonal ({(0:Fin 3),1}ᶜ)) = 4 := by
  rw [deleted_diagonal]
  norm_num [totalMass,rowSum,Matrix.diagonal_apply,Fin.sum_univ_succ]
example : originalRowAvoidance unequalDiagonal = 1 := by
  rw [originalRowAvoidance,rowAvoidance_normalizeRows,rowAvoidance_square_eq_permanent]
  norm_num [unequalDiagonal,Matrix.permanent_diagonal,rowSum,Matrix.diagonal_apply,
    Fin.prod_univ_succ,Fin.sum_univ_succ]
example : deletedRowAvoidance unequalDiagonal 0 1 = 0 := by
  rw [deletedRowAvoidance,deleted_diagonal,rowAvoidance_normalizeRows,rowAvoidance_square_eq_permanent]
  norm_num [Matrix.permanent_diagonal,rowSum,Matrix.diagonal_apply,Fin.prod_univ_succ,Fin.sum_univ_succ]
example : originalRowAvoidance unequalDiagonal ≠ deletedRowAvoidance unequalDiagonal 0 1 := by
  rw [originalRowAvoidance,deletedRowAvoidance,deleted_diagonal,
    rowAvoidance_normalizeRows,rowAvoidance_normalizeRows,
    rowAvoidance_square_eq_permanent,rowAvoidance_square_eq_permanent]
  norm_num [unequalDiagonal,Matrix.permanent_diagonal,rowSum,Matrix.diagonal_apply,
    Fin.prod_univ_succ,Fin.sum_univ_succ]

-- The strip cap is unconditional for every actual contender with m≥128.
example {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n) (P : Board m n)
    (hP : IsProbability P) (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    (j : Fin n) : (∑ i, P i j) < 1/(n:ℝ)+1/(m:ℝ)^4 :=
  endpoint_contender_column_cap_large hm hmn hP hcont j

#print axioms separationProbability_endpoint_ratios
#print axioms endpoint_contender_deficit_budget
#print axioms endpoint_contender_rows_pos
#print axioms endpoint_contender_original_collision_relation
#print axioms endpoint_contender_columnVariance
#print axioms endpoint_contender_rowProduct_deficit
#print axioms endpointRowProduct_coordinate_envelope
#print axioms endpoint_contender_column_cap_large
#print axioms normalizeRows_normalizeBoard
#print axioms deleted_rook_normalization

end DittertRybin.Test
