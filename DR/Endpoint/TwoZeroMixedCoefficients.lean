import DR.Endpoint.TwoZeroMixedRepeat
import DR.Endpoint.TwoZeroMixedStability

/-! Exact coefficient/permanent identities for arbitrary signed matrices.
The coefficients of the actual reduced bivariate polynomial are the two
repeated-row permanents divided by two and the original permanent. -/
namespace DittertRybin

private theorem quadratic_square_expansion (c : ℝ) :
    MvPolynomial.C c*(MvPolynomial.X (0 : Fin 2)+MvPolynomial.X 1)^2 =
      MvPolynomial.monomial (Finsupp.single 0 2) c+
        MvPolynomial.monomial (squarefreeExponent 2) (2*c)+
        MvPolynomial.monomial (Finsupp.single 1 2) c := by
  have htwo : MvPolynomial.C (2 : ℝ) = (2 : MvPolynomial (Fin 2) ℝ) := by
    have he : (2 : ℝ) = 1+1 := by ring
    rw [he,map_add,map_one]
    ring
  simp [MvPolynomial.monomial_eq,Finsupp.prod_fintype,squarefreeExponent_apply]
  rw [htwo]
  ring

private theorem quadratic_square_coefficient (c : ℝ) :
    (MvPolynomial.C c*(MvPolynomial.X (0 : Fin 2)+MvPolynomial.X 1)^2).coeff
      (squarefreeExponent 2) = 2*c := by
  rw [quadratic_square_expansion]
  norm_num [MvPolynomial.coeff_monomial,squarefreeExponent,Finsupp.ext_iff,Fin.forall_fin_two]

theorem homogeneous_quadratic_repeat_coeff20 {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous 2) :
    (p.eval₂ MvPolynomial.C (repeatPolynomialVariable 0 1)).coeff (squarefreeExponent 2) =
      2*p.coeff (Finsupp.single 0 2) := by
  have heval : p.eval₂ MvPolynomial.C (repeatPolynomialVariable 0 1) =
      MvPolynomial.C (p.coeff (Finsupp.single 0 2))*(MvPolynomial.X 0+MvPolynomial.X 1)^2 := by
    conv_lhs => rw [homogeneous_fin_two_quadratic hp]
    simp [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype,squarefreeExponent_apply,
      repeatPolynomialVariable]
  rw [heval,quadratic_square_coefficient]

theorem homogeneous_quadratic_repeat_coeff02 {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous 2) :
    (p.eval₂ MvPolynomial.C (repeatPolynomialVariable 1 0)).coeff (squarefreeExponent 2) =
      2*p.coeff (Finsupp.single 1 2) := by
  have heval : p.eval₂ MvPolynomial.C (repeatPolynomialVariable 1 0) =
      MvPolynomial.C (p.coeff (Finsupp.single 1 2))*(MvPolynomial.X 0+MvPolynomial.X 1)^2 := by
    conv_lhs => rw [homogeneous_fin_two_quadratic hp]
    simp [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype,squarefreeExponent_apply,
      repeatPolynomialVariable,add_comm]
  rw [heval,quadratic_square_coefficient]

/-- Repeating the penultimate row identifies the pure first coefficient. -/
theorem permanentMixedQuadratic_coeff20 {n : ℕ} (A : Board (n+2) (n+2)) :
    (permanentMixedQuadratic A).coeff (Finsupp.single (0 : Fin 2) 2) =
      (A.updateRow (Fin.natAdd n 1) (A (Fin.natAdd n 0))).permanent/2 := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (squarefreeExponent 2))
    (permanentMixedQuadratic_repeat_row A 0 1 (by decide))
  rw [permanentMixedQuadratic_coeff11,
    homogeneous_quadratic_repeat_coeff20 (permanentMixedQuadratic_homogeneous A)] at h
  linarith

/-- Repeating the final row identifies the pure second coefficient. -/
theorem permanentMixedQuadratic_coeff02 {n : ℕ} (A : Board (n+2) (n+2)) :
    (permanentMixedQuadratic A).coeff (Finsupp.single (1 : Fin 2) 2) =
      (A.updateRow (Fin.natAdd n 0) (A (Fin.natAdd n 1))).permanent/2 := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (squarefreeExponent 2))
    (permanentMixedQuadratic_repeat_row A 1 0 (by decide))
  rw [permanentMixedQuadratic_coeff11,
    homogeneous_quadratic_repeat_coeff02 (permanentMixedQuadratic_homogeneous A)] at h
  linarith


/-- The actual repeated-row permanent inequality, with zero rows and columns
retained. Nonnegativity is used only by the separately proved stable quadratic. -/
theorem permanent_repeated_rows_inequality {n : ℕ} {A : Board (n+2) (n+2)}
    (hA : ∀ i j, 0 ≤ A i j) :
    (A.updateRow (Fin.natAdd n 1) (A (Fin.natAdd n 0))).permanent*
      (A.updateRow (Fin.natAdd n 0) (A (Fin.natAdd n 1))).permanent ≤ A.permanent^2 := by
  have h := permanentMixedQuadratic_discriminant hA
  rw [permanentMixedQuadratic_coeff20,permanentMixedQuadratic_coeff02] at h
  nlinarith only [h]

end DittertRybin
