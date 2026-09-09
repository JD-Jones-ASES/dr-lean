import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact rational tensor Bernstein certificates

A certificate proves an equality of rational multivariate polynomials after
affine normalization of a rational box. Nonnegative tensor Bernstein weights
sum to one on the entire closed unit cube. Consequently a lower bound on every
rational coefficient is a lower bound on the represented polynomial, including
the boundary. A positive margin gives strict positivity. The final denominator
lemmas retain the explicit sign and cleared-identity obligations.

This is the certificate family used by the scalar and tensor box checks in the
Lab square-endpoint proof. The K=3 and order-four Gram certificates have separate
matrix-positivity and orbit-identity obligations; this module does not certify
those obligations or any Dittert inequality by itself.
-/

namespace DittertRybin.Certificates

noncomputable section

open scoped BigOperators

/-- One Bernstein coordinate index for every variable. -/
abbrev BernsteinIndex {d : ℕ} (degree : Fin d → ℕ) := ∀ i, Fin (degree i + 1)

/-- The exact rational tensor Bernstein basis polynomial. -/
def tensorBasis {d : ℕ} (degree : Fin d → ℕ) (a : BernsteinIndex degree) :
    MvPolynomial (Fin d) ℚ :=
  ∏ i, MvPolynomial.C ((degree i).choose (a i) : ℚ) *
    MvPolynomial.X i ^ (a i : ℕ) * (1 - MvPolynomial.X i) ^ (degree i - a i)

/-- The polynomial represented by the complete rational coefficient table. -/
def tensorPolynomial {d : ℕ} (degree : Fin d → ℕ) (c : BernsteinIndex degree → ℚ) :
    MvPolynomial (Fin d) ℚ := ∑ a, MvPolynomial.C (c a) * tensorBasis degree a

/-- Real evaluation of a rational polynomial; coefficients are cast exactly. -/
def rationalEval {d : ℕ} (x : Fin d → ℝ) (p : MvPolynomial (Fin d) ℚ) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) x p

/-- The scalar Bernstein weight, including its binomial normalization. -/
def bernsteinWeight (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

theorem bernsteinWeight_nonneg (n i : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinWeight n i x := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- The binomial coefficient is essential: the normalized basis sums to one. -/
theorem bernsteinWeight_sum (n : ℕ) (x : ℝ) :
    (∑ i : Fin (n + 1), bernsteinWeight n i x) = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa only [Polynomial.eval_finsetSum, Finset.sum_range, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, bernsteinWeight] using h

theorem rationalEval_tensorBasis {d : ℕ} (degree : Fin d → ℕ)
    (a : BernsteinIndex degree) (x : Fin d → ℝ) :
    rationalEval x (tensorBasis degree a) = ∏ i, bernsteinWeight (degree i) (a i) (x i) := by
  simp [rationalEval, tensorBasis, bernsteinWeight]

theorem tensorBasis_nonneg {d : ℕ} (degree : Fin d → ℕ) (a : BernsteinIndex degree)
    (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ rationalEval x (tensorBasis degree a) := by
  rw [rationalEval_tensorBasis]
  exact Finset.prod_nonneg fun i _ ↦ bernsteinWeight_nonneg _ _ (hx i).1 (hx i).2

/-- The entire tensor basis, with no missing index, forms a partition of one. -/
theorem tensorBasis_sum {d : ℕ} (degree : Fin d → ℕ) (x : Fin d → ℝ) :
    (∑ a : BernsteinIndex degree, rationalEval x (tensorBasis degree a)) = 1 := by
  simp only [rationalEval_tensorBasis]
  rw [← Fintype.prod_sum (fun i (a : Fin (degree i + 1)) ↦ bernsteinWeight (degree i) a (x i))]
  simp only [bernsteinWeight_sum, Finset.prod_const_one]

theorem rationalEval_tensorPolynomial {d : ℕ} (degree : Fin d → ℕ)
    (c : BernsteinIndex degree → ℚ) (x : Fin d → ℝ) :
    rationalEval x (tensorPolynomial degree c) =
      ∑ a, (c a : ℝ) * rationalEval x (tensorBasis degree a) := by
  simp [rationalEval, tensorPolynomial]

/-- A one-variable table reduces to an ordinary finite Bernstein sum. -/
theorem tensorPolynomial_one (n : ℕ) (c : Fin (n + 1) → ℚ) :
    tensorPolynomial (fun _ : Fin 1 ↦ n) (fun a ↦ c (a 0)) =
      ∑ a : Fin (n + 1), MvPolynomial.C (c a) *
        (MvPolynomial.C (n.choose a : ℚ) * MvPolynomial.X (0 : Fin 1) ^ (a : ℕ) *
          (1 - MvPolynomial.X (0 : Fin 1)) ^ (n - a)) := by
  unfold tensorPolynomial
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (n + 1)))
  intro a
  simp [tensorBasis, Equiv.funUnique, Equiv.piUnique]

/-- A coefficient margin is a semantic lower bound on the full closed cube. -/
theorem tensorPolynomial_lower_bound {d : ℕ} (degree : Fin d → ℕ)
    (c : BernsteinIndex degree → ℚ) (margin : ℚ) (hc : ∀ a, margin ≤ c a)
    (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (margin : ℝ) ≤ rationalEval x (tensorPolynomial degree c) := by
  rw [rationalEval_tensorPolynomial]
  calc
    (margin : ℝ) = ∑ a, (margin : ℝ) * rationalEval x (tensorBasis degree a) := by
      rw [← Finset.mul_sum, tensorBasis_sum, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun a _ ↦
      mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (hc a)) (tensorBasis_nonneg degree a x hx)

/-- Substitute `lo + (hi-lo) t`, keeping the normalization as an exact rational polynomial. -/
def affineNormalize {d : ℕ} (lo hi : Fin d → ℚ) (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin d) ℚ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i ↦ MvPolynomial.C (lo i) + MvPolynomial.C (hi i - lo i) * MvPolynomial.X i) p

theorem rationalEval_affineNormalize {d : ℕ} (lo hi : Fin d → ℚ)
    (p : MvPolynomial (Fin d) ℚ) (t : Fin d → ℝ) :
    rationalEval t (affineNormalize lo hi p) =
      rationalEval (fun i ↦ (lo i : ℝ) + ((hi i : ℝ) - lo i) * t i) p := by
  unfold rationalEval affineNormalize
  rw [← MvPolynomial.eval₂_assoc]
  simp

/-- Unit coordinates of a point in a nondegenerate rational box. -/
def boxCoordinates {d : ℕ} (lo hi : Fin d → ℚ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ (x i - lo i) / ((hi i : ℝ) - lo i)

theorem boxCoordinates_mem_unit {d : ℕ} (lo hi : Fin d → ℚ)
    (hwidth : ∀ i, lo i < hi i) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) :
    ∀ i, 0 ≤ boxCoordinates lo hi x i ∧ boxCoordinates lo hi x i ≤ 1 := by
  intro i
  have hd : (0 : ℝ) < (hi i : ℝ) - lo i := sub_pos.mpr (Rat.cast_lt.mpr (hwidth i))
  refine ⟨div_nonneg (sub_nonneg.mpr (hx i).1) hd.le, ?_⟩
  exact (div_le_one hd).mpr (sub_le_sub_right (hx i).2 _)

theorem affine_boxCoordinates {d : ℕ} (lo hi : Fin d → ℚ) (hwidth : ∀ i, lo i < hi i)
    (x : Fin d → ℝ) :
    (fun i ↦ (lo i : ℝ) + ((hi i : ℝ) - lo i) * boxCoordinates lo hi x i) = x := by
  funext i
  have hd : (hi i : ℝ) - lo i ≠ 0 := ne_of_gt (sub_pos.mpr (Rat.cast_lt.mpr (hwidth i)))
  dsimp [boxCoordinates]
  field_simp
  ring

/-- Exact coefficient identity plus exact coefficient bounds prove the box bound. -/
theorem bernstein_box_lower_bound {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (lo hi : Fin d → ℚ) (hwidth : ∀ i, lo i < hi i)
    (degree : Fin d → ℕ) (c : BernsteinIndex degree → ℚ) (margin : ℚ)
    (hidentity : affineNormalize lo hi p = tensorPolynomial degree c)
    (hcoeff : ∀ a, margin ≤ c a) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) :
    (margin : ℝ) ≤ rationalEval x p := by
  have h := tensorPolynomial_lower_bound degree c margin hcoeff (boxCoordinates lo hi x)
    (boxCoordinates_mem_unit lo hi hwidth x hx)
  rw [← hidentity, rationalEval_affineNormalize, affine_boxCoordinates lo hi hwidth] at h
  exact h

/-- Strict coefficient margin proves strict positivity, including every box face. -/
theorem bernstein_box_pos {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (lo hi : Fin d → ℚ) (hwidth : ∀ i, lo i < hi i)
    (degree : Fin d → ℕ) (c : BernsteinIndex degree → ℚ) (margin : ℚ)
    (hidentity : affineNormalize lo hi p = tensorPolynomial degree c)
    (hcoeff : ∀ a, margin ≤ c a) (hmargin : 0 < margin) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) : 0 < rationalEval x p :=
  lt_of_lt_of_le (Rat.cast_pos.mpr hmargin)
    (bernstein_box_lower_bound p lo hi hwidth degree c margin hidentity hcoeff x hx)

/-- It suffices to check the literal rational coefficients on the union of both supports. -/
theorem polynomial_eq_of_support_coefficients {d : ℕ} (p q : MvPolynomial (Fin d) ℚ)
    (h : ∀ a ∈ p.support ∪ q.support, p.coeff a = q.coeff a) : p = q := by
  classical
  apply MvPolynomial.ext
  intro a
  by_cases ha : a ∈ p.support ∪ q.support
  · exact h a ha
  · simp only [Finset.mem_union, not_or] at ha
    have hp : p.coeff a = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using ha.1
    have hq : q.coeff a = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using ha.2
    rw [hp, hq]

/-- A proof-carrying exact rational certificate. No numerical or status field is accepted. -/
structure BernsteinCertificate {d : ℕ} (p : MvPolynomial (Fin d) ℚ) (lo hi : Fin d → ℚ) where
  degree : Fin d → ℕ
  coefficients : BernsteinIndex degree → ℚ
  margin : ℚ
  identity : affineNormalize lo hi p = tensorPolynomial degree coefficients
  coefficient_bound : ∀ a, margin ≤ coefficients a

theorem BernsteinCertificate.lower_bound {d : ℕ} {p : MvPolynomial (Fin d) ℚ}
    {lo hi : Fin d → ℚ} (cert : BernsteinCertificate p lo hi) (hwidth : ∀ i, lo i < hi i)
    (x : Fin d → ℝ) (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) :
    (cert.margin : ℝ) ≤ rationalEval x p :=
  bernstein_box_lower_bound p lo hi hwidth cert.degree cert.coefficients cert.margin
    cert.identity cert.coefficient_bound x hx

theorem BernsteinCertificate.pos {d : ℕ} {p : MvPolynomial (Fin d) ℚ}
    {lo hi : Fin d → ℚ} (cert : BernsteinCertificate p lo hi) (hwidth : ∀ i, lo i < hi i)
    (hmargin : 0 < cert.margin) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) : 0 < rationalEval x p :=
  lt_of_lt_of_le (Rat.cast_pos.mpr hmargin) (cert.lower_bound hwidth x hx)

/-- Division preserves the certified positive gap only with a positive denominator. -/
theorem BernsteinCertificate.div_pos {d : ℕ} {p : MvPolynomial (Fin d) ℚ}
    {lo hi : Fin d → ℚ} (cert : BernsteinCertificate p lo hi) (hwidth : ∀ i, lo i < hi i)
    (hmargin : 0 < cert.margin) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) (D : ℝ) (hD : 0 < D) :
    0 < rationalEval x p / D := _root_.div_pos (cert.pos hwidth hmargin x hx) hD

/-- A certified numerator transfers through a proved cleared-denominator identity. -/
theorem BernsteinCertificate.cleared_denominator_pos {d : ℕ} {p : MvPolynomial (Fin d) ℚ}
    {lo hi : Fin d → ℚ} (cert : BernsteinCertificate p lo hi) (hwidth : ∀ i, lo i < hi i)
    (hmargin : 0 < cert.margin) (x : Fin d → ℝ)
    (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) (D gap : ℝ) (hD : 0 < D)
    (hcleared : rationalEval x p = D * gap) : 0 < gap := by
  have h := cert.pos hwidth hmargin x hx
  rw [hcleared] at h
  exact pos_of_mul_pos_right h hD.le

/-- The exact margin also survives division with its required scale factor. -/
theorem BernsteinCertificate.cleared_denominator_lower_bound {d : ℕ}
    {p : MvPolynomial (Fin d) ℚ} {lo hi : Fin d → ℚ}
    (cert : BernsteinCertificate p lo hi) (hwidth : ∀ i, lo i < hi i)
    (x : Fin d → ℝ) (hx : ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i)
    (D gap : ℝ) (hD : 0 < D) (hcleared : rationalEval x p = D * gap) :
    (cert.margin : ℝ) / D ≤ gap := by
  apply (div_le_iff₀ hD).mpr
  rw [mul_comm, ← hcleared]
  exact cert.lower_bound hwidth x hx

end

end DittertRybin.Certificates
