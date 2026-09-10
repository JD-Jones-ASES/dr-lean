import DR.Endpoint.TwoZeroMixedStability

namespace DittertRybin

example (p : MvPolynomial (Fin 2) ℝ) : permanentQuadraticReduce 0 p = p := rfl

example {n : ℕ} (p : MvPolynomial (Fin (n+2)) ℝ)
    (hhom : p.IsHomogeneous (n+2)) (hc : HasNonnegativeCoefficients p)
    (hp : p = 0 ∨ HStable p) :
    permanentQuadraticReduce n p = 0 ∨ HStable (permanentQuadraticReduce n p) :=
  permanentQuadraticReduce_zero_or_hStable n hhom hc hp

example : matrixProductPolynomial (0 : Board 3 3) = 0 ∨
    HStable (matrixProductPolynomial (0 : Board 3 3)) :=
  matrixProductPolynomial_zero_or_hStable (by simp)

example : matrixProductPolynomial (!![1,2;0,0] : Board 2 2) = 0 := by
  norm_num [matrixProductPolynomial, Fin.prod_univ_succ, Fin.sum_univ_succ]

example {n : ℕ} (A : Board (n+2) (n+2)) :
    (permanentMixedQuadratic A).IsHomogeneous 2 := permanentMixedQuadratic_homogeneous A

example {n : ℕ} (A : Board (n+2) (n+2)) (hA : ∀ i j, 0 ≤ A i j) :
    4*(permanentMixedQuadratic A).coeff (Finsupp.single 0 2)*
      (permanentMixedQuadratic A).coeff (Finsupp.single 1 2) ≤ A.permanent^2 :=
  permanentMixedQuadratic_discriminant hA

#print axioms permanentQuadraticReduce_homogeneous
#print axioms permanentQuadraticReduce_nonnegative
#print axioms permanentQuadraticReduce_zero_or_hStable
#print axioms matrixProductPolynomial_zero_or_hStable
#print axioms permanentMixedQuadratic_zero_or_hStable
#print axioms permanentMixedQuadratic_discriminant

end DittertRybin
