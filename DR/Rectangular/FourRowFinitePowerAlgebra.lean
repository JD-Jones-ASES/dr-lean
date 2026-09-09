import DR.Rectangular.FourRowFinitePolynomialBlocks
import DR.Certificates.BernsteinTransform
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Exact coefficient arithmetic for the cleared blocks

Every product has a degree-three clearing factor and a degree-four role
numerator. Their ordinary convolution is proved equal to polynomial
multiplication, with all eight coefficients retained.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

def fourRowFinitePowerProduct (p : Fin 4 → ℚ) (q : Fin 5 → ℚ) (d : Fin 8) : ℚ :=
  ∑ k : Fin 4, if h : k.val ≤ d.val ∧ d.val-k.val < 5 then p k*q ⟨d.val-k.val,h.2⟩ else 0

theorem fourRowFinitePowerProduct_polynomial (p : Fin 4 → ℚ) (q : Fin 5 → ℚ) :
    powerPolynomial (fourRowFinitePowerProduct p q) = powerPolynomial p*powerPolynomial q := by
  apply MvPolynomial.funext
  intro x
  simp [powerPolynomial, fourRowFinitePowerProduct, Fin.sum_univ_succ]
  ring

theorem fourRowFinitePower_add {d : ℕ} (p q : Fin (d+1) → ℚ) :
    powerPolynomial (fun k => p k+q k) = powerPolynomial p+powerPolynomial q := by
  simp [powerPolynomial, map_add, add_mul, Finset.sum_add_distrib]

theorem fourRowFinitePower_sub {d : ℕ} (p q : Fin (d+1) → ℚ) :
    powerPolynomial (fun k => p k-q k) = powerPolynomial p-powerPolynomial q := by
  simp [powerPolynomial, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem fourRowFinitePower_scale {d : ℕ} (c : ℚ) (p : Fin (d+1) → ℚ) :
    powerPolynomial (fun k => c*p k) = C c*powerPolynomial p := by
  simp [powerPolynomial, map_mul, Finset.mul_sum, mul_assoc]

def fourRowFiniteDenominatorPower (a : ℕ) : Fin 4 → ℚ :=
  ![1,-6/(a : ℚ),11/(a : ℚ)^2,-6/(a : ℚ)^3]

def fourRowFiniteColumnClearingPower (a : ℕ) (q : Fin 3) : Fin 4 → ℚ :=
  (![![0,1/(a : ℚ),-5/(a : ℚ)^2,6/(a : ℚ)^3],
     ![0,1/(a : ℚ),-4/(a : ℚ)^2,3/(a : ℚ)^3],
     ![0,1/(a : ℚ),-3/(a : ℚ)^2,2/(a : ℚ)^3]] : Fin 3 → Fin 4 → ℚ) q

theorem fourRowFiniteDenominatorPower_polynomial (a : ℕ) :
    powerPolynomial (fourRowFiniteDenominatorPower a) = fourRowFinitePolynomialDenominator a := by
  apply MvPolynomial.funext
  intro x
  simp [powerPolynomial, fourRowFiniteDenominatorPower, fourRowFinitePolynomialDenominator,
    Fin.sum_univ_succ, Fin.prod_univ_succ, div_eq_mul_inv]
  ring

theorem fourRowFiniteColumnClearingPower_polynomial (a : ℕ) (q : Fin 3) :
    powerPolynomial (fourRowFiniteColumnClearingPower a q) =
      fourRowFinitePolynomialColumnClearing a q := by
  fin_cases q
  all_goals
    apply MvPolynomial.funext
    intro x
  · have he : Finset.univ.erase (0 : Fin 3) = {1,2} := by decide
    simp [powerPolynomial, fourRowFiniteColumnClearingPower,
      fourRowFinitePolynomialColumnClearing, he, Fin.sum_univ_succ, div_eq_mul_inv]
    ring
  · have he : Finset.univ.erase (1 : Fin 3) = {0,2} := by decide
    simp [powerPolynomial, fourRowFiniteColumnClearingPower,
      fourRowFinitePolynomialColumnClearing, he, Fin.sum_univ_succ, div_eq_mul_inv]
    ring
  · have he : Finset.univ.erase (2 : Fin 3) = {0,1} := by decide
    simp [powerPolynomial, fourRowFiniteColumnClearingPower,
      fourRowFinitePolynomialColumnClearing, he, Fin.sum_univ_succ, div_eq_mul_inv]
    ring

/-- Padding the degree-seven vector by two zeros is an exact identity, not truncation. -/
def fourRowFinitePowerPad (p : Fin 8 → ℚ) (k : Fin 10) : ℚ :=
  if h : k.val < 8 then p ⟨k.val,h⟩ else 0

theorem fourRowFinitePowerPad_polynomial (p : Fin 8 → ℚ) :
    powerPolynomial (fourRowFinitePowerPad p) = powerPolynomial p := by
  simp [powerPolynomial, fourRowFinitePowerPad, Fin.sum_univ_succ]

end
end DittertRybin
