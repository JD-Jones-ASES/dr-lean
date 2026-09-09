import DR.Rectangular.FourRowFiniteBernstein

namespace DittertRybin.Certificates
open scoped BigOperators

private def linearExample : Fin 2 → Matrix (Fin 1) (Fin 1) ℚ :=
  fun _ _ _ => 1

private theorem linearExample_coefficients (k : Fin 2) :
    ((fourRowFiniteMatrixBernstein (1/10) 1 linearExample k).map
      (fun q : ℚ => (q : ℝ))) =
      Matrix.diagonal (fun _ : Fin 1 => if k = 0 then 11/10 else 2) := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fourRowFiniteMatrixBernstein, powerToBernstein, affinePowerCoefficients,
      linearExample, Fin.sum_univ_succ]

example (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteMatrixPolynomial linearExample u).PosDef := by
  apply fourRowFiniteMatrixPolynomial_posDef (1/10) 1 linearExample (by norm_num) _ u
    (by simpa using hu)
  intro k
  rw [linearExample_coefficients]
  apply Matrix.PosDef.diagonal
  intro i
  split_ifs <;> norm_num

example : fourRowFiniteMatrixPolynomial linearExample (1/10) 0 0 = 11/10 := by
  norm_num [fourRowFiniteMatrixPolynomial_eval, linearExample, Fin.sum_univ_succ]

example : fourRowFiniteMatrixPolynomial linearExample 1 0 0 = 2 := by
  norm_num [fourRowFiniteMatrixPolynomial_eval, linearExample, Fin.sum_univ_succ]

example : (∑ k : Fin 10, bernsteinWeight 9 k 0) = 1 := bernsteinWeight_sum 9 0
example : (∑ k : Fin 10, bernsteinWeight 9 k 1) = 1 := bernsteinWeight_sum 9 1

example (p : Fin 10 → Matrix (Fin 0) (Fin 0) ℚ) (u : ℝ) :
    fourRowFiniteMatrixPolynomial p u = (1 : Matrix (Fin 0) (Fin 0) ℝ) := by
  ext i
  exact Fin.elim0 i

example : ¬ (Matrix.of (fun _ _ : Fin 1 => (-1 : ℝ))).PosDef := by
  intro h
  have hp := h.diag_pos (i := (0 : Fin 1))
  norm_num at hp

#print axioms quadraticValue_weighted_matrix_sum
#print axioms posDef_weighted_matrix_sum
#print axioms fourRowFiniteMatrixPolynomial_bernstein
#print axioms fourRowFiniteMatrixPolynomial_posDef
#print axioms fourRowFiniteMatrixPolynomial_cleared_posDef

end DittertRybin.Certificates
