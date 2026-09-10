import DR.Endpoint.StableQuadratic

namespace DittertRybin
open MvPolynomial

example : (0 : ℝ) ≤ 0 := by
  have h := stable_fin_two_quadratic_discriminant
    (p := (0 : MvPolynomial (Fin 2) ℝ)) (MvPolynomial.isHomogeneous_zero _ _ 2) (Or.inl rfl)
  simpa only [MvPolynomial.coeff_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)] using h

example (p : MvPolynomial (Fin 2) ℝ) (hhom : p.IsHomogeneous 2)
    (hp : HStable p) :
    4*p.coeff (Finsupp.single 0 2)*p.coeff (Finsupp.single 1 2) ≤
      (p.coeff (squarefreeExponent 2))^2 :=
  stable_fin_two_quadratic_discriminant hhom (Or.inr hp)

example (b c : ℝ)
    (hp : (Polynomial.C (0 : ℝ)*Polynomial.X^2+Polynomial.C b*Polynomial.X+
      Polynomial.C c).Splits) : 0 ≤ b^2 := by
  simpa using split_quadratic_discriminant 0 b c hp

example (p : MvPolynomial (Fin 2) ℝ) (hhom : p.IsHomogeneous 2)
    (hp : p.coeff (Finsupp.single 0 2) = 1)
    (hq : p.coeff (Finsupp.single 1 2) = 1)
    (hr : p.coeff (squarefreeExponent 2) = 0) : ¬HStable p := by
  intro hs
  have h := stable_fin_two_quadratic_discriminant hhom (Or.inr hs)
  norm_num [hp,hq,hr] at h

example (p : MvPolynomial (Fin 2) ℝ) (hhom : p.IsHomogeneous 2)
    (h20 : p.coeff (Finsupp.single 0 2) = 0)
    (h11 : p.coeff (squarefreeExponent 2) = 0)
    (h02 : p.coeff (Finsupp.single 1 2) = 0) : p = 0 := by
  rw [homogeneous_fin_two_quadratic hhom, h20,h11,h02]
  simp

/-- The discriminant inequality is sharp at the repeated-root boundary. -/
example : (Polynomial.C (1 : ℝ)*Polynomial.X^2+Polynomial.C 2*Polynomial.X+
    Polynomial.C 1).Splits := by
  have hneg := (Polynomial.Splits.X_sub_C (-1 : ℝ)).pow 2
  have heq : Polynomial.C (1 : ℝ)*Polynomial.X^2+Polynomial.C 2*Polynomial.X+
      Polynomial.C 1 = (Polynomial.X-Polynomial.C (-1))^2 := by
    rw [show Polynomial.C (2 : ℝ) = (2 : Polynomial ℝ) by
      exact map_ofNat Polynomial.C 2]
    norm_num
    ring
  rw [heq]
  exact hneg

example : (4 : ℝ)*1*1 = 2^2 := by norm_num

#print axioms homogeneous_fin_two_quadratic
#print axioms homogeneous_fin_two_slice
#print axioms split_quadratic_discriminant
#print axioms stable_fin_two_quadratic_discriminant

end DittertRybin
