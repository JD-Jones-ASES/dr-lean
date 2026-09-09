import DR.Square.StableDerivative
import DR.Square.PermanentCoefficient

/-! Boundary controls for stable differentiation and the permanent coefficient. -/

open DittertRybin MvPolynomial

-- A nonzero stable homogeneous polynomial can vanish after differentiation at zero.
example : derivativeAtZero ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ 2) 0 = 0 := by
  simp [derivativeAtZero]

-- A mixed squarefree monomial loses exactly the differentiated variable.
example : derivativeAtZero ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) * X 1) 0 = X 1 := by
  simp [derivativeAtZero]

-- Empty products give coefficient and permanent one, not zero.
example (A : Board 0 0) : (matrixProductPolynomial A).coeff (squarefreeExponent 0) = 1 := by
  rw [matrixProductPolynomial_squarefree_coefficient]
  exact Matrix.permanent_eq_one_of_card_eq_zero (by simp)

-- Every constant matrix includes the correct factorial multiplicity.
example (n : ℕ) (c : ℝ) :
    (matrixProductPolynomial (fun (_ _ : Fin n) => c)).coeff (squarefreeExponent n) =
      n.factorial * c ^ n := by
  exact (matrixProductPolynomial_squarefree_coefficient (fun (_ _ : Fin n) => c)).trans
    (by simpa using (permanent_const (ι := Fin n) c))
