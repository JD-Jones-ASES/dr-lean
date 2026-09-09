import DR.ElementarySymmetricBoundsVariance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace DittertRybin.Test
open scoped BigOperators
open Polynomial

-- This full type is the actual canonical Rook sum, with no positivity of support.
example {d k : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hk : 2 ≤ k) (hkd : k ≤ d) :
    (elementarySymmetric x k/(d.choose k:ℝ))^2 ≤
      (elementarySymmetric x 2/(d.choose 2:ℝ))^k :=
  elementaryMean_maclaurin_two hx hk hkd

-- Mass one and the exact dimension/order factors are exposed in the release type.
example {d k : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (he : 1-epsilon ≤ (d:ℝ)^k *
      (∑ e : Fin k ↪o Fin d, ∏ t, x (e t))/(d.choose k:ℝ)) :
    (∑ i, (x i-1/(d:ℝ))^2) ≤
      2*((d:ℝ)-1)*epsilon/((d:ℝ)*k*(1-epsilon)) := by
  apply marginalVariance_le_of_elementary_success hx hs hk hkd he0 he1
  simpa only [normalizedElementarySuccess,elementaryMean,elementarySymmetric,mul_div_assoc] using he

-- Empty products retain their exact degree-zero normalization.
example : elementarySymmetric (fun _ : Fin 0 => (7:ℝ)) 0 = 1 := by
  rw [elementarySymmetric_const]
  norm_num
example : normalizedElementarySuccess (fun _ : Fin 4 => (1:ℝ)/4) 0 = 1 :=
  normalizedElementarySuccess_uniform (by norm_num) (by norm_num)

-- Repeated roots are allowed, and evaluation at a root requires no division.
example : (elementaryRootPolynomial (fun _ : Fin 3 => (2:ℝ))).derivative.Splits :=
  real_splits_derivative (elementaryRootPolynomial_splits _)
example : (3:ℝ) * (elementaryRootPolynomial (fun _ : Fin 3 => (2:ℝ))).eval (-2) *
      (elementaryRootPolynomial (fun _ : Fin 3 => (2:ℝ))).derivative.derivative.eval (-2) ≤
    2*((elementaryRootPolynomial (fun _ : Fin 3 => (2:ℝ))).derivative.eval (-2))^2 := by
  simpa only [elementaryRootPolynomial_natDegree,Nat.cast_ofNat,show (3:ℝ)-1=2 by norm_num] using
    real_splits_laguerre (elementaryRootPolynomial_splits (fun _ : Fin 3 => (2:ℝ)))
      (by rw [elementaryRootPolynomial_natDegree]; norm_num) (-2)

-- The splitting hypothesis is substantive: X²+1 violates the claimed inequality at zero.
example : ¬ ((2:ℝ)*(X^2+1 : ℝ[X]).eval 0*(X^2+1 : ℝ[X]).derivative.derivative.eval 0 ≤
    (2-1)*((X^2+1 : ℝ[X]).derivative.eval 0)^2) := by
  norm_num [Polynomial.derivative_add,Polynomial.derivative_pow]

-- The binomial normalization is indispensable even at a constant vector.
example : elementaryMean (fun _ : Fin 4 => (1:ℝ)) 3 = 1 := by
  norm_num [elementaryMean,elementarySymmetric_const,Nat.choose]
example : ¬ ((elementarySymmetric (fun _ : Fin 4 => (1:ℝ)) 0)*
    elementarySymmetric (fun _ : Fin 4 => (1:ℝ)) 2 ≤
    (elementaryMean (fun _ : Fin 4 => (1:ℝ)) 1)^2) := by
  norm_num [elementaryMean,elementarySymmetric_const,Nat.choose]

-- A sparse vector lies on the closed boundary; degree two and degree three differ.
private noncomputable def sparseThree : Fin 3 → ℝ := ![1/2,1/2,0]
private theorem sparseThree_nonneg : ∀ i, 0 ≤ sparseThree i := by
  intro i
  fin_cases i <;> norm_num [sparseThree]
private theorem sparseThree_sum : ∑ i, sparseThree i = 1 := by
  norm_num [sparseThree,Fin.sum_univ_succ]
example : marginalVariance sparseThree = 1/6 := by
  norm_num [marginalVariance,sparseThree,Fin.sum_univ_succ]
example : normalizedElementarySuccess sparseThree 2 = 3/4 := by
  rw [normalizedElementarySuccess_two (by norm_num) sparseThree_sum]
  norm_num [marginalVariance,sparseThree,Fin.sum_univ_succ]
example : normalizedElementarySuccess sparseThree 3 < 1 := by
  have hle := normalizedElementarySuccess_le_one sparseThree_nonneg sparseThree_sum
    (k := 3) (by norm_num) (by norm_num)
  have hne : normalizedElementarySuccess sparseThree 3 ≠ 1 := by
    intro h
    have hu := (normalizedElementarySuccess_eq_one_iff sparseThree_nonneg sparseThree_sum
      (k := 3) (by norm_num) (by norm_num)).mp h (2 : Fin 3)
    change (0:ℝ) = 1/3 at hu
    norm_num at hu
  exact lt_of_le_of_ne hle hne

-- The lower-order guard is substantive: order one cannot force uniformity.
example : normalizedElementarySuccess (![1,0] : Fin 2 → ℝ) 1 = 1 := by
  rw [normalizedElementarySuccess,elementaryMean,
    ← elementaryRootPolynomial_coeff _ (by norm_num : 1 ≤ 2)]
  norm_num [elementaryRootPolynomial,Fin.prod_univ_two]
example : ¬ (∀ i : Fin 2, (![1,0] : Fin 2 → ℝ) i = 1/2) := by
  intro h
  have h0 := h 0
  norm_num at h0

-- Zero deficit gives equality on every coordinate, including an initially closed domain.
example {d k : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d)
    (he : normalizedElementarySuccess x k = 1) : ∀ i, x i = 1/(d:ℝ) :=
  (normalizedElementarySuccess_eq_one_iff hx hs hk hkd).mp he

#print axioms real_splits_derivative
#print axioms real_splits_laguerre
#print axioms normalizedCoefficient_newton
#print axioms elementaryMean_newton
#print axioms elementaryMean_maclaurin_two
#print axioms normalizedElementarySuccess_variance_bound
#print axioms marginalVariance_le_of_elementary_success
#print axioms normalizedElementarySuccess_eq_one_iff

end DittertRybin.Test
