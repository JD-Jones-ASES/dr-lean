import DR.Rectangular.FourRowFinitePolynomialBlocks
import Mathlib.Algebra.MvPolynomial.Funext

namespace DittertRybin
open MvPolynomial Certificates
noncomputable section

example : fourRowFinitePolynomialDenominator 5 =
    1-C (6/5)*X 0+C (11/25)*(X 0)^2-C (6/125)*(X 0)^3 := by
  apply MvPolynomial.funext
  intro x
  norm_num [fourRowFinitePolynomialDenominator, Fin.prod_univ_succ]
  ring

example : fourRowFinitePolynomialColumnClearing 5 2 =
    C (1/5)*X 0-C (3/25)*(X 0)^2+C (2/125)*(X 0)^3 := by
  have he : Finset.univ.erase (2 : Fin 3) = {0,1} := by decide
  rw [fourRowFinitePolynomialColumnClearing, he]
  apply MvPolynomial.funext
  intro x
  norm_num
  ring

-- The literal polynomial identities themselves permit negative parameters.
example : rationalEval (fun _ => (-2 : ℝ)) (fourRowFinitePolynomialDenominator 5) = 693/125 := by
  rw [fourRowFinitePolynomialDenominator_eval]
  norm_num [fourRowFiniteDenominator, Fin.prod_univ_succ]

-- This is the actual R=1, C=2 averaged entry for a signed constant role polynomial.
example : rationalEval (fun _ => (1 : ℝ))
    (fourRowFiniteTrivialPolynomial 3 2 5 (fun _ => C (-2)) [] (3,3) (3,3)) = -48/125 := by
  rw [fourRowFiniteTrivialPolynomial_eval (by norm_num) (by norm_num) (by norm_num)]
  norm_num [fourRowFiniteDenominator, fourRowFiniteTrivialEntry, fourRowFiniteOrdinaryAverage,
    fourRowFiniteRealRoleEntry, rationalEval, Fin.prod_univ_succ]

example (a nr : ℕ) (q : Fin 3) (p : FourRowFiniteUnivariate) (mark : List (ℕ × ℕ)) :
    fourRowFiniteInteractionPolynomial nr q a (fun _ => p) mark = 0 := by
  simp [fourRowFiniteInteractionPolynomial, fourRowFinitePolynomialRoleEntry]

#print axioms fourRowFinitePolynomialDenominator_eval
#print axioms fourRowFinitePolynomialColumnClearing_eval
#print axioms fourRowFiniteTrivialPolynomial_eval
#print axioms fourRowFiniteRowStandardPolynomial_eval
#print axioms fourRowFiniteColumnStandardPolynomial_eval
#print axioms fourRowFiniteInteractionPolynomial_eval

end
end DittertRybin
