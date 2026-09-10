import DR.Endpoint.TwoZeroMixedSubstitution

/-! Actual row duplication agrees with a substitution in the row-product
polynomial. All entries may be signed. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def repeatPolynomialVariable {N : ℕ} (a b j : Fin N) :
    MvPolynomial (Fin N) ℝ :=
  if j=a then MvPolynomial.X a+MvPolynomial.X b else if j=b then 0 else MvPolynomial.X j

theorem permanentLiftSubstitution_repeat (n : ℕ) (a b : Fin 2) :
    permanentLiftSubstitution n (repeatPolynomialVariable a b) =
      repeatPolynomialVariable (Fin.natAdd n a) (Fin.natAdd n b) := by
  induction n with
  | zero =>
    have ha : Fin.natAdd 0 a = a := by ext; simp
    have hb : Fin.natAdd 0 b = b := by ext; simp
    rw [ha,hb]
    rfl
  | succ n ih =>
    have ha : Fin.natAdd (n+1) a = (Fin.natAdd n a).succ := by ext; simp; omega
    have hb : Fin.natAdd (n+1) b = (Fin.natAdd n b).succ := by ext; simp; omega
    funext j
    rw [permanentLiftSubstitution,ih]
    cases j using Fin.cases with
    | zero =>
      simp only [liftPolynomialSubstitution,Fin.cases_zero,repeatPolynomialVariable,ha,hb]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero _)),if_neg (Ne.symm (Fin.succ_ne_zero _))]
    | succ j =>
      by_cases hja : j = Fin.natAdd n a <;> by_cases hjb : j = Fin.natAdd n b <;>
        by_cases hba : b=a <;>
        simp [liftPolynomialSubstitution,repeatPolynomialVariable,ha,hb,hja,hjb,hba]

theorem matrixProductPolynomial_repeat_row {N : ℕ} (A : Board N N)
    (a b : Fin N) (hab : a ≠ b) :
    matrixProductPolynomial (A.updateRow b (A a)).transpose =
      (matrixProductPolynomial A.transpose).eval₂ MvPolynomial.C (repeatPolynomialVariable a b) := by
  classical
  unfold matrixProductPolynomial
  simp only [MvPolynomial.eval₂_prod,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,MvPolynomial.eval₂_X,Matrix.transpose_apply]
  apply Finset.prod_congr rfl
  intro j _
  have hleft : (∑ i, MvPolynomial.C ((A.updateRow b (A a)) i j)*MvPolynomial.X i) =
      (∑ i, MvPolynomial.C (A i j)*MvPolynomial.X i)+
        (MvPolynomial.C (A a j)-MvPolynomial.C (A b j))*MvPolynomial.X b := by
    have heach (i : Fin N) : MvPolynomial.C ((A.updateRow b (A a)) i j)*MvPolynomial.X i =
        MvPolynomial.C (A i j)*MvPolynomial.X i+
          (if i=b then (MvPolynomial.C (A a j)-MvPolynomial.C (A b j))*MvPolynomial.X b else 0) := by
      by_cases hi : i=b
      · subst i; simp [Matrix.updateRow_apply]; ring
      · simp [Matrix.updateRow_apply,hi]
    simp only [heach,Finset.sum_add_distrib]
    simp
  rw [hleft]
  have heach (i : Fin N) : MvPolynomial.C (A i j)*repeatPolynomialVariable a b i =
      MvPolynomial.C (A i j)*MvPolynomial.X i+
        (if i=a then MvPolynomial.C (A a j)*MvPolynomial.X b else 0)-
        (if i=b then MvPolynomial.C (A b j)*MvPolynomial.X b else 0) := by
    by_cases hia : i=a
    · subst i; simp [repeatPolynomialVariable,hab]; ring
    · by_cases hib : i=b
      · subst i; simp [repeatPolynomialVariable,Ne.symm hab]
      · simp [repeatPolynomialVariable,hia,hib]
  simp only [heach,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp
  ring

theorem permanentMixedQuadratic_repeat_row {n : ℕ} (A : Board (n+2) (n+2))
    (a b : Fin 2) (hab : a ≠ b) :
    permanentMixedQuadratic (A.updateRow (Fin.natAdd n b) (A (Fin.natAdd n a))) =
      (permanentMixedQuadratic A).eval₂ MvPolynomial.C (repeatPolynomialVariable a b) := by
  unfold permanentMixedQuadratic
  rw [matrixProductPolynomial_repeat_row A _ _ ((Fin.natAdd_injective 2 n).ne hab),
    ← permanentLiftSubstitution_repeat,permanentQuadraticReduce_substitution]

end DittertRybin
