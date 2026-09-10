import DR.Square.StableSlices
import DR.Square.PermanentCoefficient
import Mathlib.Algebra.QuadraticDiscriminant

/-! The exact discriminant inequality for a homogeneous stable quadratic in
two variables. Zero polynomials and missing square terms are retained. -/

namespace DittertRybin
open scoped BigOperators

private theorem degree_two_fin_two (d : Fin 2 →₀ ℕ) (hd : d.degree = 2) :
    d = Finsupp.single 0 2 ∨ d = squarefreeExponent 2 ∨ d = Finsupp.single 1 2 := by
  have hs : d 0+d 1 = 2 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have heq (e : Fin 2 →₀ ℕ) (h0 : d 0 = e 0) (h1 : d 1 = e 1) : d = e := by
    ext i
    fin_cases i <;> assumption
  have hcases : (d 0 = 2 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 1) ∨
      (d 0 = 0 ∧ d 1 = 2) := by omega
  rcases hcases with h | h | h
  · exact Or.inl (heq _ (by simpa using h.1) (by simpa using h.2))
  · exact Or.inr (Or.inl (heq _ (by simpa [squarefreeExponent_apply] using h.1)
      (by simpa [squarefreeExponent_apply] using h.2)))
  · exact Or.inr (Or.inr (heq _ (by simpa using h.1) (by simpa using h.2)))

theorem homogeneous_fin_two_quadratic {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous 2) :
    p = MvPolynomial.monomial (Finsupp.single 0 2) (p.coeff (Finsupp.single 0 2)) +
      MvPolynomial.monomial (squarefreeExponent 2) (p.coeff (squarefreeExponent 2)) +
      MvPolynomial.monomial (Finsupp.single 1 2) (p.coeff (Finsupp.single 1 2)) := by
  classical
  ext d
  by_cases hd : d.degree = 2
  · rcases degree_two_fin_two d hd with rfl | rfl | rfl <;>
      norm_num [MvPolynomial.coeff_monomial, squarefreeExponent,
        Finsupp.ext_iff, Fin.forall_fin_two]
  · have hz := hp.coeff_eq_zero hd
    have h20 : Finsupp.single (0 : Fin 2) 2 ≠ d := by
      intro h; apply hd; rw [← h]; simp
    have h02 : Finsupp.single (1 : Fin 2) 2 ≠ d := by
      intro h; apply hd; rw [← h]; simp
    have h11 : squarefreeExponent 2 ≠ d := by
      intro h; apply hd; rw [← h]
      simp [Finsupp.degree_eq_sum, squarefreeExponent_apply]
    simp [MvPolynomial.coeff_monomial, hz, h20, h02, h11]

theorem homogeneous_fin_two_slice {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous 2) :
    singleVariableSlice p 0 (fun _ => 1) =
      Polynomial.C (p.coeff (Finsupp.single 0 2))*Polynomial.X^2 +
      Polynomial.C (p.coeff (squarefreeExponent 2))*Polynomial.X +
      Polynomial.C (p.coeff (Finsupp.single 1 2)) := by
  conv_lhs => rw [homogeneous_fin_two_quadratic hp]
  simp [singleVariableSlice, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype, squarefreeExponent_apply]

/-- A real quadratic that splits has nonnegative discriminant. A missing
leading coefficient is included and requires no choice of a root. -/
theorem split_quadratic_discriminant (a b c : ℝ)
    (hp : (Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+
      Polynomial.C c).Splits) : 4*a*c ≤ b^2 := by
  by_cases ha : a = 0
  · simp [ha, sq_nonneg]
  · have hdeg : (Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+
        Polynomial.C c).degree ≠ 0 := by
      intro h
      have hlt : (Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+
          Polynomial.C c).degree < (2 : WithBot ℕ) := by rw [h]; norm_num
      have hc := Polynomial.coeff_eq_zero_of_degree_lt
        (p := Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c)
        (n := 2) hlt
      simp at hc
      exact ha hc
    obtain ⟨x, hx⟩ := hp.exists_eval_eq_zero hdeg
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hx
    have hd := discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by nlinarith only [hx])
    unfold discrim at hd
    nlinarith [sq_nonneg (2*a*x+b)]

/-- The coefficient form of Alexandrov's reverse Cauchy inequality for the
stable quadratic. The zero-polynomial alternative is explicit. -/
theorem stable_fin_two_quadratic_discriminant {p : MvPolynomial (Fin 2) ℝ}
    (hhom : p.IsHomogeneous 2) (hp : p = 0 ∨ HStable p) :
    4*p.coeff (Finsupp.single 0 2)*p.coeff (Finsupp.single 1 2) ≤
      (p.coeff (squarefreeExponent 2))^2 := by
  have hs := singleVariableSlice_splits_of_zero_or_hStable hhom hp 0
    (x := fun _ => 1) (fun _ => by norm_num)
  rw [homogeneous_fin_two_slice hhom] at hs
  exact split_quadratic_discriminant _ _ _ hs

end DittertRybin
