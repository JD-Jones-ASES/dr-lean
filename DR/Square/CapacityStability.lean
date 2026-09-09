import DR.Square.CapacityMatrix
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# The initial homogeneous H-stable matrix polynomial

H-stability here means nonvanishing whenever every complex coordinate has
strictly positive real part. The product of nonnegative row linear forms
is H-stable when every row has positive mass. This module establishes only
the starting polynomial; derivative and boundary-specialization closure
remain separate obligations in Gurvits's argument (arXiv:0711.3496v2).
-/

open scoped BigOperators
open Finset Set Matrix MvPolynomial

namespace DittertRybin

/-- Nonvanishing on the product of open complex right half-planes. -/
def HStable {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).re) → p.eval₂ (algebraMap ℝ ℂ) z ≠ 0

theorem HStable.ne_zero {σ : Type*} {p : MvPolynomial σ ℝ} (hp : HStable p) : p ≠ 0 := by
  intro hzero
  have h := hp (fun _ => 1) (by intro i; norm_num)
  simp [hzero] at h

/-- Coefficient nonnegativity is recorded independently of stability. -/
def HasNonnegativeCoefficients {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ d, 0 ≤ p.coeff d

theorem hasNonnegativeCoefficients_one {σ : Type*} :
    HasNonnegativeCoefficients (1 : MvPolynomial σ ℝ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_one]
  split_ifs <;> norm_num

theorem hasNonnegativeCoefficients_X {σ : Type*} (i : σ) :
    HasNonnegativeCoefficients (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

theorem HasNonnegativeCoefficients.mul {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (hq : HasNonnegativeCoefficients q) :
    HasNonnegativeCoefficients (p * q) := by
  classical
  intro d
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hp e.1) (hq e.2)

theorem HasNonnegativeCoefficients.C_mul {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) {c : ℝ} (hc : 0 ≤ c) :
    HasNonnegativeCoefficients (MvPolynomial.C c * p) := by
  intro d
  rw [MvPolynomial.coeff_C_mul]
  exact mul_nonneg hc (hp d)

theorem hasNonnegativeCoefficients_sum {σ ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i ∈ s, HasNonnegativeCoefficients (p i)) :
    HasNonnegativeCoefficients (∑ i ∈ s, p i) := by
  intro d
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg fun i hi => hp i hi d

theorem hasNonnegativeCoefficients_prod {σ ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i ∈ s, HasNonnegativeCoefficients (p i)) :
    HasNonnegativeCoefficients (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNonnegativeCoefficients_one (σ := σ)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hp i (by simp)).mul (ih (fun j hj => hp j (by simp [hj])))

theorem hStable_prod {σ ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ s, HStable (p i)) : HStable (∏ i ∈ s, p i) := by
  intro z hz
  rw [MvPolynomial.eval₂_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => hp i hi z hz

/-- The row-linear-form product as an ordinary multivariate polynomial. -/
noncomputable def matrixProductPolynomial {n : ℕ} (A : Board n n) : MvPolynomial (Fin n) ℝ :=
  ∏ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

theorem matrixProductPolynomial_eval {n : ℕ} (A : Board n n) (x : Fin n → ℝ) :
    (matrixProductPolynomial A).eval x = matrixProduct A x := by
  simp [matrixProductPolynomial, matrixProduct]

theorem matrixProductPolynomial_eval₂ {n : ℕ} (A : Board n n) (z : Fin n → ℂ) :
    (matrixProductPolynomial A).eval₂ (algebraMap ℝ ℂ) z =
      ∏ i, ∑ j, (A i j : ℂ) * z j := by
  simp [matrixProductPolynomial]

theorem matrixProductPolynomial_isHomogeneous {n : ℕ} (A : Board n n) :
    (matrixProductPolynomial A).IsHomogeneous n := by
  have hrow (i : Fin n) :
      (∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j).IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
      (fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [matrixProductPolynomial] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) (fun _ => 1)
    (fun i _ => hrow i)

theorem matrixProductPolynomial_nonnegative {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) : HasNonnegativeCoefficients (matrixProductPolynomial A) := by
  apply hasNonnegativeCoefficients_prod
  intro i hi
  apply hasNonnegativeCoefficients_sum
  intro j hj
  exact (hasNonnegativeCoefficients_X j).C_mul (hA i j)

/-- A nonzero nonnegative real linear form has positive real part on this domain. -/
theorem realPart_sum_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : 0 < ∑ i, a i) {z : Fin n → ℂ} (hz : ∀ i, 0 < (z i).re) :
    0 < (∑ i, (a i : ℂ) * z i).re := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_pos'
  · exact fun i _ => mul_nonneg (ha i) (hz i).le
  · obtain ⟨i, hi, hai⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => ha i)).mp hs
    exact ⟨i, hi, mul_pos hai (hz i)⟩

theorem matrixProductPolynomial_hStable {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, 0 < rowSum A i) :
    HStable (matrixProductPolynomial A) := by
  intro z hz
  rw [matrixProductPolynomial_eval₂]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have h := realPart_sum_pos (hA i) (hrow i) hz
  intro hzero
  rw [hzero, Complex.zero_re] at h
  exact (lt_irrefl 0) h

theorem matrixProductPolynomial_hStable_of_doublyStochastic {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) : HStable (matrixProductPolynomial A) :=
  matrixProductPolynomial_hStable (fun i j => nonneg_of_mem_doublyStochastic hA)
    (fun i => by change 0 < ∑ j, A i j; rw [sum_row_of_mem_doublyStochastic hA i]; norm_num)

/-- Capacity one stated on the actual multivariate polynomial's evaluation. -/
theorem matrixProductPolynomial_capacity_eq_one {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    multivariateCapacity (fun x => (matrixProductPolynomial A).eval x) = 1 := by
  have heval : (fun x => (matrixProductPolynomial A).eval x) = matrixProduct A :=
    funext (matrixProductPolynomial_eval A)
  rw [heval]
  exact matrixProduct_capacity_eq_one hA

end DittertRybin
