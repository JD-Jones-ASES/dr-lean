import DR.Square.CapacityBound

/-! The actual bivariate row-product polynomial left after eliminating the
first n matrix-row variables. These are algebraic definitions on arbitrary
signed matrices; stability and face minimization are separate layers. -/
namespace DittertRybin

noncomputable def permanentQuadraticReduce : (n : ℕ) →
    MvPolynomial (Fin (n+2)) ℝ → MvPolynomial (Fin 2) ℝ
  | 0, p => p
  | n+1, p => permanentQuadraticReduce n (capacityReduce p)

noncomputable def permanentMixedQuadratic {n : ℕ} (A : Board (n+2) (n+2)) :
    MvPolynomial (Fin 2) ℝ := permanentQuadraticReduce n (matrixProductPolynomial A.transpose)

/-- Restoring the eliminated coordinates puts exponent one in each of them. -/
noncomputable def permanentQuadraticExponent : (n : ℕ) →
    (Fin 2 →₀ ℕ) → (Fin (n+2) →₀ ℕ)
  | 0, d => d
  | n+1, d => (permanentQuadraticExponent n d).cons 1

theorem permanentQuadraticReduce_coeff (n : ℕ) (p : MvPolynomial (Fin (n+2)) ℝ)
    (d : Fin 2 →₀ ℕ) :
    (permanentQuadraticReduce n p).coeff d = p.coeff (permanentQuadraticExponent n d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [permanentQuadraticReduce,ih,capacityReduce_coeff]
    rfl

theorem permanentQuadraticExponent_squarefree (n : ℕ) :
    permanentQuadraticExponent n (squarefreeExponent 2) = squarefreeExponent (n+2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [permanentQuadraticExponent,ih,squarefreeExponent_cons]

theorem permanentMixedQuadratic_coeff11 {n : ℕ} (A : Board (n+2) (n+2)) :
    (permanentMixedQuadratic A).coeff (squarefreeExponent 2) = A.permanent := by
  rw [permanentMixedQuadratic,permanentQuadraticReduce_coeff,
    permanentQuadraticExponent_squarefree,matrixProductPolynomial_squarefree_coefficient,
    Matrix.permanent_transpose]

end DittertRybin
