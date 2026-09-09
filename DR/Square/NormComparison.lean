import DR.Square.StableSlices

/-!
# Homogeneous H-stable norm comparison

This proves the norm comparison in Gurvits (2008), Section 4,
https://arxiv.org/abs/0711.3496v2. The line q(t)=p(X+tY), X positive and
Y real, has only real roots. Comparing its real linear factors at i and
zero yields the norm comparison without a limit or closure assumption.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

/-- A real line through a positive vector, represented as a real polynomial. -/
noncomputable def realLinePolynomial {σ : Type*} (p : MvPolynomial σ ℝ)
    (x y : σ → ℝ) : Polynomial ℝ :=
  p.eval₂ Polynomial.C (fun j => Polynomial.C (x j) + Polynomial.C (y j) * Polynomial.X)

theorem realLinePolynomial_eval₂ {σ S : Type*} [CommSemiring S]
    (p : MvPolynomial σ ℝ) (x y : σ → ℝ) (f : ℝ →+* S) (t : S) :
    (realLinePolynomial p x y).eval₂ f t =
      p.eval₂ f (fun j => f (x j) + f (y j) * t) := by
  change (Polynomial.eval₂RingHom f t)
    (p.eval₂ Polynomial.C (fun j => Polynomial.C (x j) + Polynomial.C (y j) * Polynomial.X)) = _
  rw [MvPolynomial.eval₂_comp_left, Polynomial.eval₂RingHom_comp_C]
  congr 1
  funext j
  simp

theorem exists_realPart_one_multiplier_product_realPart_zero {z : ℂ} (hz : z.im ≠ 0) :
    ∃ w : ℂ, w.re = 1 ∧ (w * z).re = 0 := by
  refine ⟨⟨1, z.re / z.im⟩, rfl, ?_⟩
  simp only [Complex.mul_re]
  field_simp
  ring

/-- A common multiplier carries a putative nonreal line zero into the domain. -/
theorem realLinePolynomial_complex_root_real {σ : Type*} {p : MvPolynomial σ ℝ}
    {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p) {x y : σ → ℝ}
    (hx : ∀ j, 0 < x j) {z : ℂ}
    (hzero : (realLinePolynomial p x y).eval₂ (algebraMap ℝ ℂ) z = 0) : z.im = 0 := by
  by_contra him
  obtain ⟨w, hw, hwz⟩ := exists_realPart_one_multiplier_product_realPart_zero him
  have heval : p.eval₂ (algebraMap ℝ ℂ)
      (fun j => (algebraMap ℝ ℂ) (x j) + (algebraMap ℝ ℂ) (y j) * z) = 0 := by
    rw [← realLinePolynomial_eval₂]
    exact hzero
  have hright : ∀ j, 0 < (w * ((algebraMap ℝ ℂ) (x j) + (algebraMap ℝ ℂ) (y j) * z)).re := by
    intro j
    have heq : w * ((algebraMap ℝ ℂ) (x j) + (algebraMap ℝ ℂ) (y j) * z) =
        (algebraMap ℝ ℂ) (x j) * w + (algebraMap ℝ ℂ) (y j) * (w * z) := by ring
    rw [heq]
    simpa [Complex.mul_re, hw, hwz] using hx j
  apply hp _ hright
  rw [homogeneous_eval₂_scale hhom, heval, mul_zero]

theorem realLinePolynomial_splits {σ : Type*} {p : MvPolynomial σ ℝ}
    {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p) {x y : σ → ℝ}
    (hx : ∀ j, 0 < x j) : (realLinePolynomial p x y).Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
  intro z hz
  have hzero : (realLinePolynomial p x y).eval₂ (algebraMap ℝ ℂ) z = 0 := by
    rw [← Polynomial.eval_map]
    exact Polynomial.isRoot_of_mem_roots hz
  have him := realLinePolynomial_complex_root_real hhom hp hx hzero
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [him]

/-- Real-rooted polynomials grow in modulus from zero to the imaginary unit.
This includes the zero polynomial and roots at zero. -/
theorem splits_norm_eval_zero_le_eval_I {q : Polynomial ℝ} (hq : q.Splits) :
    ‖q.eval₂ (algebraMap ℝ ℂ) (0 : ℂ)‖ ≤ ‖q.eval₂ (algebraMap ℝ ℂ) Complex.I‖ := by
  classical
  let l := q.roots.toList
  have hfactor : q = Polynomial.C q.leadingCoeff *
      ∏ j : Fin l.length, (Polynomial.X - Polynomial.C l[j.1]) := by
    calc
      q = _ := hq.eq_prod_roots
      _ = _ := congrArg (fun v => Polynomial.C q.leadingCoeff * v)
        ((Multiset.prod_map_toList q.roots (fun r => Polynomial.X - Polynomial.C r)).symm.trans
          (Fin.prod_univ_fun_getElem l (fun r => Polynomial.X - Polynomial.C r)).symm)
  conv_lhs => rw [hfactor]
  conv_rhs => rw [hfactor]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
  intro j hj
  simpa [Complex.coe_algebraMap, Real.norm_eq_abs] using
    Complex.abs_re_le_norm (Complex.I - (l[j.1] : ℂ))

/-- Gurvits's homogeneous norm comparison on the open right-half-plane domain. -/
theorem homogeneous_hStable_norm_comparison {σ : Type*} {p : MvPolynomial σ ℝ}
    {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p) {z : σ → ℂ}
    (hz : ∀ j, 0 < (z j).re) :
    ‖p.eval₂ (algebraMap ℝ ℂ) (fun j => (algebraMap ℝ ℂ) (z j).re)‖ ≤
      ‖p.eval₂ (algebraMap ℝ ℂ) z‖ := by
  have h := splits_norm_eval_zero_le_eval_I
    (realLinePolynomial_splits hhom hp hz (y := fun j => (z j).im))
  rw [realLinePolynomial_eval₂, realLinePolynomial_eval₂] at h
  simpa only [mul_zero, add_zero, Complex.coe_algebraMap, Complex.re_add_im] using h

theorem eval₂_of_real_vector {σ : Type*} (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    p.eval₂ (algebraMap ℝ ℂ) (fun j => (algebraMap ℝ ℂ) (x j)) =
      (algebraMap ℝ ℂ) (p.eval x) := by
  simpa [Function.comp_def] using
    (MvPolynomial.eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ) x p).symm

/-- The same comparison with ordinary real evaluation on the left. -/
theorem homogeneous_hStable_norm_comparison_real {σ : Type*} {p : MvPolynomial σ ℝ}
    {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p) {z : σ → ℂ}
    (hz : ∀ j, 0 < (z j).re) :
    ‖p.eval (fun j => (z j).re)‖ ≤ ‖p.eval₂ (algebraMap ℝ ℂ) z‖ := by
  have h := homogeneous_hStable_norm_comparison hhom hp hz
  rw [eval₂_of_real_vector] at h
  simpa using h

end DittertRybin
