import DR.Endpoint.TwoZeroMixedDefinitions

/-! Exact commutation of coefficient elimination with substitutions in the
remaining variables. No positivity or stability hypothesis is used. -/
namespace DittertRybin

noncomputable def liftPolynomialSubstitution {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) ℝ) : Fin (n+1) → MvPolynomial (Fin (n+1)) ℝ :=
  Fin.cases (MvPolynomial.X 0) (fun j => MvPolynomial.rename Fin.succ (f j))

theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [map_mul,MvPolynomial.rename_X,hp,MvPolynomial.finSuccEquiv_X_succ]

theorem finSuccEquiv_lift_substitution {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin (n+1)) ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (p.eval₂ MvPolynomial.C (liftPolynomialSubstitution f)) =
      Polynomial.map (MvPolynomial.eval₂Hom MvPolynomial.C f) (MvPolynomial.finSuccEquiv ℝ n p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [MvPolynomial.eval₂_add,map_add,Polynomial.map_add,hp,hq]
  | mul_X p j hp =>
    simp only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,map_mul,Polynomial.map_mul,hp]
    congr 1
    cases j using Fin.cases with
    | zero => simp [liftPolynomialSubstitution,MvPolynomial.finSuccEquiv_X_zero]
    | succ j => simp [liftPolynomialSubstitution,finSuccEquiv_rename_succ,
        MvPolynomial.finSuccEquiv_X_succ]

theorem capacityReduce_lift_substitution {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin (n+1)) ℝ) :
    capacityReduce (p.eval₂ MvPolynomial.C (liftPolynomialSubstitution f)) =
      (capacityReduce p).eval₂ MvPolynomial.C f := by
  unfold capacityReduce
  rw [finSuccEquiv_lift_substitution,Polynomial.coeff_map]
  rfl

noncomputable def permanentLiftSubstitution : (n : ℕ) →
    (Fin 2 → MvPolynomial (Fin 2) ℝ) → (Fin (n+2) → MvPolynomial (Fin (n+2)) ℝ)
  | 0, f => f
  | n+1, f => liftPolynomialSubstitution (permanentLiftSubstitution n f)

theorem permanentQuadraticReduce_substitution (n : ℕ)
    (f : Fin 2 → MvPolynomial (Fin 2) ℝ) (p : MvPolynomial (Fin (n+2)) ℝ) :
    permanentQuadraticReduce n (p.eval₂ MvPolynomial.C (permanentLiftSubstitution n f)) =
      (permanentQuadraticReduce n p).eval₂ MvPolynomial.C f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [permanentLiftSubstitution,permanentQuadraticReduce,capacityReduce_lift_substitution,ih]
    rfl

end DittertRybin
