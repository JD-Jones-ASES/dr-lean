import DR.Square.StableDerivative

/-!
# Capacity descent by an actual derivative and dimension reduction

The reduction is coefficient one in `finSuccEquiv`: differentiate coordinate
zero, specialize it to zero, and remove that coordinate from the index type.
-/

open scoped BigOperators Topology Polynomial
open Finset Set Filter

namespace DittertRybin

/-- Differentiate coordinate zero, specialize it to zero, and remove it. -/
noncomputable def capacityReduce {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := (MvPolynomial.finSuccEquiv ℝ n p).coeff 1

theorem capacityReduce_coeff {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin n →₀ ℕ) : (capacityReduce p).coeff m = p.coeff (m.cons 1) :=
  MvPolynomial.finSuccEquiv_coeff_coeff m p 1

theorem capacityReduce_nonnegative {n : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hp : HasNonnegativeCoefficients p) : HasNonnegativeCoefficients (capacityReduce p) := by
  intro m
  rw [capacityReduce_coeff]
  exact hp _

theorem capacityReduce_isHomogeneous {n d : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hp : p.IsHomogeneous (d + 1)) : (capacityReduce p).IsHomogeneous d := by
  exact hp.finSuccEquiv_coeff_isHomogeneous 1 d (by omega)

private theorem finSuccEquiv_map_eq_affineLine {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin n → ℂ) :
    Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z)
      (MvPolynomial.finSuccEquiv ℝ n p) =
        affineLinePolynomial p (Fin.cons 0 z) (fun j => if j = 0 then 1 else 0) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply, affineLinePolynomial]
  | add p q hp hq => simpa [affineLinePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    rw [map_mul, Polynomial.map_mul, hp]
    simp only [affineLinePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    congr 1
    cases j using Fin.cases with
    | zero => simp [MvPolynomial.finSuccEquiv_X_zero]
    | succ j => simp [MvPolynomial.finSuccEquiv_X_succ]

theorem capacityReduce_eval₂ {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (z : Fin n → ℂ) :
    (capacityReduce p).eval₂ (algebraMap ℝ ℂ) z =
      (derivativeAtZero p 0).eval₂ (algebraMap ℝ ℂ) (Fin.cons 1 z) := by
  have hcoeff : (capacityReduce p).eval₂ (algebraMap ℝ ℂ) z =
      (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z)
        (MvPolynomial.finSuccEquiv ℝ n p)).derivative.eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, Polynomial.coeff_map]
    simp [capacityReduce]
  rw [hcoeff, finSuccEquiv_map_eq_affineLine, affineLinePolynomial_derivative_eval_zero,
    directionalDerivative_single, derivativeAtZero_eq_scaleVariables, scaleVariables_eval₂]
  congr 1
  funext j
  cases j using Fin.cases <;> simp

theorem capacityReduce_eval {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (x : Fin n → ℝ) : (capacityReduce p).eval x =
      (singleVariableSlice p 0 (Fin.cons 1 x)).derivative.eval 0 := by
  have h := capacityReduce_eval₂ p (fun j => (algebraMap ℝ ℂ) (x j))
  have heq : Fin.cons 1 (fun j => (algebraMap ℝ ℂ) (x j)) =
      fun j : Fin (n + 1) => (algebraMap ℝ ℂ) ((Fin.cons (1 : ℝ) x : Fin (n + 1) → ℝ) j) := by
    funext j
    cases j using Fin.cases <;> simp
  rw [heq, eval₂_of_real_vector, eval₂_of_real_vector] at h
  exact (Complex.ofReal_injective h).trans (derivativeAtZero_eval p 0 (Fin.cons 1 x))

theorem capacityReduce_zero_or_hStable {n d : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hhom : p.IsHomogeneous d) (hc : HasNonnegativeCoefficients p)
    (hp : p = 0 ∨ HStable p) : capacityReduce p = 0 ∨ HStable (capacityReduce p) := by
  rcases derivativeAtZero_zero_or_hStable hhom hc hp 0 with hd | hd
  · left
    by_contra hred
    have hpos := mvPolynomial_eval_pos (capacityReduce_nonnegative hc) hred
      (x := fun _ => 1) (fun _ => by norm_num)
    have heval := capacityReduce_eval₂ p (fun _ => 1)
    rw [hd, MvPolynomial.eval₂_zero] at heval
    have hreal : (capacityReduce p).eval (fun _ => 1) = 0 := by
      have heq : (fun _ : Fin n => (1 : ℂ)) = fun _ => (algebraMap ℝ ℂ) (1 : ℝ) := by simp
      rw [heq, eval₂_of_real_vector] at heval
      exact Complex.ofReal_eq_zero.mp heval
    exact hpos.ne' hreal
  · right
    intro z hz
    rw [capacityReduce_eval₂]
    apply hd
    intro j
    cases j using Fin.cases
    · norm_num
    · exact hz _

/-- Capacity is nonnegative when the polynomial has nonnegative coefficients. -/
theorem polynomial_multivariateCapacity_nonneg {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hc : HasNonnegativeCoefficients p) : 0 ≤ multivariateCapacity (fun x => p.eval x) := by
  apply le_multivariateCapacity
  intro x hx
  exact div_nonneg (mvPolynomial_eval_nonneg hc (fun j => (hx j).le))
    (Finset.prod_pos fun j _ => hx j).le

theorem singleVariableSlice_zero_eval {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    (singleVariableSlice p 0 (Fin.cons 1 x)).eval t = p.eval (Fin.cons t x) := by
  have h := singleVariableSlice_eval₂ p 0 (Fin.cons 1 x) (RingHom.id ℝ) t
  simp only [Polynomial.eval₂_id, RingHom.id_apply, MvPolynomial.eval₂_id] at h
  rw [h]
  congr 2
  funext j
  cases j using Fin.cases <;> simp

/-- Fixing the remaining positive variables gives a lower bound on slice
capacity directly from the defining multivariate infimum. -/
theorem multivariateCapacity_mul_prod_le_slice_capacity {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) ℝ} (hc : HasNonnegativeCoefficients p)
    {x : Fin n → ℝ} (hx : ∀ j, 0 < x j) :
    multivariateCapacity (fun y => p.eval y) * ∏ j, x j ≤
      univariateCapacity (fun t => (singleVariableSlice p 0 (Fin.cons 1 x)).eval t) := by
  apply le_univariateCapacity
  intro t ht
  have hcons : ∀ j : Fin (n + 1), 0 < (Fin.cons t x : Fin (n + 1) → ℝ) j := by
    intro j
    cases j using Fin.cases
    · exact ht
    · exact hx _
  have h := multivariateCapacity_le
    (fun y hy => mvPolynomial_eval_nonneg hc (fun j => (hy j).le)) hcons
  rw [Fin.prod_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [le_div_iff₀ (mul_pos ht (Finset.prod_pos fun j _ => hx j))] at h
  rw [singleVariableSlice_zero_eval, le_div_iff₀ ht]
  convert h using 1
  ring

/-- One actual derivative and dimension reduction loses at most the univariate
factor. This is an inequality between the two defined infima. -/
theorem capacityReduce_capacity_lower_bound {n d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) ℝ} (hhom : p.IsHomogeneous d)
    (hc : HasNonnegativeCoefficients p) (hp : p = 0 ∨ HStable p) (hd : 2 ≤ d) :
    capacityFactor d * multivariateCapacity (fun x => p.eval x) ≤
      multivariateCapacity (fun x => (capacityReduce p).eval x) := by
  apply le_multivariateCapacity
  intro x hx
  have hxcons : ∀ j : Fin (n + 1), 0 < (Fin.cons 1 x : Fin (n + 1) → ℝ) j := by
    intro j
    cases j using Fin.cases
    · norm_num
    · exact hx _
  have hslice := singleVariableSlice_capacity_le_deriv hhom hp hc hd 0 hxcons
  rw [← capacityReduce_eval] at hslice
  have hcap := mul_le_mul_of_nonneg_left
    (multivariateCapacity_mul_prod_le_slice_capacity hc hx) (capacityFactor_pos hd).le
  rw [le_div_iff₀ (Finset.prod_pos fun j _ => hx j)]
  calc
    capacityFactor d * multivariateCapacity (fun y => p.eval y) * ∏ j, x j =
        capacityFactor d * (multivariateCapacity (fun y => p.eval y) * ∏ j, x j) := by ring
    _ ≤ _ := hcap.trans hslice

end DittertRybin
