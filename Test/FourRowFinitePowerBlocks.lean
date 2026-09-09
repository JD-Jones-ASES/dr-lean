import DR.Rectangular.FourRowFinitePowerBlocks

namespace DittertRybin
open Certificates MvPolynomial
noncomputable section

-- The highest product coefficient is retained even when negative.
example : fourRowFinitePowerProduct ![0,0,0,-2] ![0,0,0,0,3] 7 = -6 := by
  decide +kernel

example : fourRowFinitePowerProduct ![0,0,0,-2] ![0,0,0,0,3] 7 ≠ 0 := by
  decide +kernel

example (p : Fin 8 → ℚ) : fourRowFinitePowerPad p 8 = 0 ∧
    fourRowFinitePowerPad p 9 = 0 := by simp [fourRowFinitePowerPad]

-- Denominator zero is permitted by the formal coefficient identities.
example : powerPolynomial (fourRowFiniteDenominatorPower 0) = 1 := by
  simp [fourRowFiniteDenominatorPower, powerPolynomial, Fin.sum_univ_succ]

example (q : Fin 3) : powerPolynomial (fourRowFiniteColumnClearingPower 0 q) = 0 := by
  rw [fourRowFiniteColumnClearingPower_polynomial]
  simp [fourRowFinitePolynomialColumnClearing]

-- With one ordinary row, its absent second-row sector contributes exactly zero.
example (f : ℕ → ℕ → Fin 5 → ℚ) :
    fourRowFinitePowerAverage 3 1 f 3 3 = f 3 3 := by
  funext k
  simp [fourRowFinitePowerAverage]

example (nr a : ℕ) (q : Fin 3) (h : Fin 5 → ℚ) (mark : List (ℕ × ℕ)) :
    fourRowFiniteInteractionPower nr q a (fun _ => h) mark = 0 := by
  funext k
  simp [fourRowFiniteInteractionPower, fourRowFinitePowerProduct, fourRowFiniteRolePower]

#print axioms fourRowFinitePowerProduct_polynomial
#print axioms fourRowFiniteDenominatorPower_polynomial
#print axioms fourRowFiniteColumnClearingPower_polynomial
#print axioms fourRowFinitePowerPad_polynomial
#print axioms fourRowFiniteTrivialPower_polynomial
#print axioms fourRowFiniteRowStandardPower_polynomial
#print axioms fourRowFiniteColumnStandardPower_polynomial
#print axioms fourRowFiniteInteractionPower_polynomial

end
end DittertRybin
