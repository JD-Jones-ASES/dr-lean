import DR.Square.CapacityStability
import DR.Square.CapacityPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Positive slices of a homogeneous H-stable polynomial

A common complex scaling excludes nonreal slice roots directly. This uses
homogeneity and the original H-stability condition; it does not assume any
derivative or boundary-specialization stability closure.

Source statement: Gurvits (2008), Section 4, Corollary 4.6,
https://arxiv.org/abs/0711.3496v2. The proof here uses the explicit common
complex multiplier rather than a separate hyperbolicity framework.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

/-- Homogeneity gives scaling of complex evaluation, including a zero scalar. -/
theorem homogeneous_eval₂_scale {σ : Type*} {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ℂ) (z : σ → ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) (fun i => w * z i) =
      w ^ d * p.eval₂ (algebraMap ℝ ℂ) z := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hm]
  ring

/-- A nonreal number can be scaled into the right half-plane while the
scaling factor itself has real part one. -/
theorem exists_positive_realPart_multiplier {z : ℂ} (hz : z.im ≠ 0) :
    ∃ w : ℂ, w.re = 1 ∧ (w * z).re = 1 := by
  refine ⟨⟨1, (z.re - 1) / z.im⟩, rfl, ?_⟩
  simp only [Complex.mul_re]
  field_simp
  ring

/-- Leave one variable free and evaluate the other variables at real values. -/
noncomputable def singleVariableSlice {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i : σ) (x : σ → ℝ) : Polynomial ℝ :=
  p.eval₂ Polynomial.C (fun j => if j = i then Polynomial.X else Polynomial.C (x j))

theorem singleVariableSlice_eval₂ {σ S : Type*} [DecidableEq σ] [CommSemiring S]
    (p : MvPolynomial σ ℝ) (i : σ) (x : σ → ℝ) (f : ℝ →+* S) (t : S) :
    (singleVariableSlice p i x).eval₂ f t =
      p.eval₂ f (fun j => if j = i then t else f (x j)) := by
  change (Polynomial.eval₂RingHom f t)
    (p.eval₂ Polynomial.C (fun j => if j = i then Polynomial.X else Polynomial.C (x j))) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.eval₂RingHom f t).comp Polynomial.C = f := by
    ext c
    simp
  rw [hc]
  congr 1
  funext j
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem singleVariableSlice_zero {σ : Type*} [DecidableEq σ] (i : σ) (x : σ → ℝ) :
    singleVariableSlice (0 : MvPolynomial σ ℝ) i x = 0 := by
  simp [singleVariableSlice]

theorem singleVariableSlice_ne_zero {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} (hp : HStable p) (i : σ) {x : σ → ℝ}
    (hx : ∀ j, 0 < x j) : singleVariableSlice p i x ≠ 0 := by
  intro hzero
  have h := hp (fun j => if j = i then 1 else (algebraMap ℝ ℂ) (x j)) (by
    intro j
    split_ifs <;> simp [hx])
  rw [← singleVariableSlice_eval₂ p i x (algebraMap ℝ ℂ) (1 : ℂ)] at h
  simp [hzero] at h

/-- Every complex zero of a positive slice is real and nonpositive. -/
theorem singleVariableSlice_complex_root_nonpos {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p)
    (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 < x j) {z : ℂ}
    (hzero : (singleVariableSlice p i x).eval₂ (algebraMap ℝ ℂ) z = 0) :
    z.im = 0 ∧ z.re ≤ 0 := by
  have heval : p.eval₂ (algebraMap ℝ ℂ) (fun j => if j = i then z else (algebraMap ℝ ℂ) (x j)) = 0 := by
    rw [← singleVariableSlice_eval₂ p i x (algebraMap ℝ ℂ) z]
    exact hzero
  constructor
  · by_contra him
    obtain ⟨w, hw, hwz⟩ := exists_positive_realPart_multiplier him
    have hright : ∀ j, 0 < (w * (if j = i then z else (algebraMap ℝ ℂ) (x j))).re := by
      intro j
      by_cases hji : j = i
      · simp [hji, hwz]
      · simpa [hji, Complex.mul_re, hw] using hx j
    apply hp _ hright
    rw [homogeneous_eval₂_scale hhom, heval, mul_zero]
  · by_contra! hre
    apply hp (fun j => if j = i then z else (algebraMap ℝ ℂ) (x j)) _ heval
    intro j
    split_ifs <;> simp [hre, hx]

/-- The nonpositive-root conclusion in ordinary real evaluation. -/
theorem singleVariableSlice_real_root_nonpos {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p)
    (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 < x j) {r : ℝ}
    (hr : (singleVariableSlice p i x).eval r = 0) : r ≤ 0 := by
  have hzero : (singleVariableSlice p i x).eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) r) = 0 := by
    rw [Polynomial.eval₂_at_apply, hr, map_zero]
  simpa using (singleVariableSlice_complex_root_nonpos hhom hp i hx hzero).2

/-- Complex splitting descends to real splitting because every root is real. -/
theorem singleVariableSlice_splits {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hp : HStable p)
    (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 < x j) :
    (singleVariableSlice p i x).Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ)
    (IsAlgClosed.splits _)
  intro z hz
  have hzero : (singleVariableSlice p i x).eval₂ (algebraMap ℝ ℂ) z = 0 := by
    rw [← Polynomial.eval_map]
    exact Polynomial.isRoot_of_mem_roots hz
  have him := (singleVariableSlice_complex_root_nonpos hhom hp i hx hzero).1
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [him]

/-- The zero polynomial is explicitly included for later closure alternatives. -/
theorem singleVariableSlice_splits_of_zero_or_hStable {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hp : p = 0 ∨ HStable p) (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 < x j) :
    (singleVariableSlice p i x).Splits := by
  rcases hp with rfl | hp
  · simp [singleVariableSlice_zero]
  · exact singleVariableSlice_splits hhom hp i hx

private theorem polynomial_coeff_nonneg_C {c : ℝ} (hc : 0 ≤ c) :
    ∀ k, 0 ≤ (Polynomial.C c).coeff k := by
  intro k
  simp only [Polynomial.coeff_C]
  split_ifs <;> positivity

private theorem polynomial_coeff_nonneg_X : ∀ k, 0 ≤ (Polynomial.X : Polynomial ℝ).coeff k := by
  intro k
  simp only [Polynomial.coeff_X]
  split_ifs <;> norm_num

private theorem polynomial_coeff_nonneg_mul {p q : Polynomial ℝ}
    (hp : ∀ k, 0 ≤ p.coeff k) (hq : ∀ k, 0 ≤ q.coeff k) :
    ∀ k, 0 ≤ (p * q).coeff k := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hp e.1) (hq e.2)

private theorem polynomial_coeff_nonneg_pow {p : Polynomial ℝ}
    (hp : ∀ k, 0 ≤ p.coeff k) (n : ℕ) : ∀ k, 0 ≤ (p ^ n).coeff k := by
  induction n with
  | zero => simpa using polynomial_coeff_nonneg_C (c := 1) (by norm_num)
  | succ n ih =>
    rw [pow_succ]
    exact polynomial_coeff_nonneg_mul ih hp

private theorem polynomial_coeff_nonneg_prod {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ℝ) (hp : ∀ i ∈ s, ∀ k, 0 ≤ (p i).coeff k) :
    ∀ k, 0 ≤ (∏ i ∈ s, p i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomial_coeff_nonneg_C (c := 1) (by norm_num)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact polynomial_coeff_nonneg_mul (hp i (by simp)) (ih fun j hj => hp j (by simp [hj]))

private theorem polynomial_coeff_nonneg_sum {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ℝ) (hp : ∀ i ∈ s, ∀ k, 0 ≤ (p i).coeff k) :
    ∀ k, 0 ≤ (∑ i ∈ s, p i).coeff k := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun i hi => hp i hi k

/-- Specialization at nonnegative real values preserves coefficient nonnegativity. -/
theorem singleVariableSlice_coeff_nonneg {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} (hp : HasNonnegativeCoefficients p)
    (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 ≤ x j) :
    ∀ k, 0 ≤ (singleVariableSlice p i x).coeff k := by
  unfold singleVariableSlice
  rw [MvPolynomial.eval₂_eq]
  apply polynomial_coeff_nonneg_sum
  intro m hm
  apply polynomial_coeff_nonneg_mul (polynomial_coeff_nonneg_C (hp m))
  apply polynomial_coeff_nonneg_prod
  intro j hj
  apply polynomial_coeff_nonneg_pow
  split_ifs
  · exact polynomial_coeff_nonneg_X
  · exact polynomial_coeff_nonneg_C (hx j)

/-- A slice's degree cannot exceed the homogeneous degree. -/
theorem singleVariableSlice_natDegree_le {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (i : σ) (x : σ → ℝ) :
    (singleVariableSlice p i x).natDegree ≤ d := by
  unfold singleVariableSlice
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ j ∈ m.support, m j := by
      apply Finset.sum_le_sum
      intro j hj
      apply Polynomial.natDegree_pow_le.trans
      have hv : (if j = i then Polynomial.X else Polynomial.C (x j)).natDegree ≤ 1 := by
        split_ifs <;> simp
      simpa using Nat.mul_le_mul_left (m j) hv
    _ = d := (hp.degree_eq_sum_deg_support hm).symm

/-- Every positive slice satisfies the actual univariate capacity-to-derivative
bound. The zero-polynomial alternative is retained for subsequent closure steps. -/
theorem singleVariableSlice_capacity_le_deriv {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hp : p = 0 ∨ HStable p) (hc : HasNonnegativeCoefficients p) (hd : 2 ≤ d)
    (i : σ) {x : σ → ℝ} (hx : ∀ j, 0 < x j) :
    capacityFactor d * univariateCapacity (fun t => (singleVariableSlice p i x).eval t) ≤
      (singleVariableSlice p i x).derivative.eval 0 :=
  polynomial_capacity_le_deriv (singleVariableSlice_splits_of_zero_or_hStable hhom hp i hx)
    (singleVariableSlice_coeff_nonneg hc i (fun j => (hx j).le)) hd
    (singleVariableSlice_natDegree_le hhom i x)

end DittertRybin
