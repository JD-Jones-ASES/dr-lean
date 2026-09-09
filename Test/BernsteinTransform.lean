import DR.Certificates.BernsteinTransform
import Mathlib.Tactic.FinCases

/-! Degree elevation, affine scaling, and closed-interval coefficient controls. -/

open scoped BigOperators
open DittertRybin.Certificates

private def testQuadratic : Fin 3 → ℚ := ![1, -1, 1]

example (i : Fin 3) : powerToBernstein testQuadratic i = (![1, 1/2, 1] : Fin 3 → ℚ) i := by
  fin_cases i <;> norm_num [powerToBernstein, testQuadratic, Fin.sum_univ_succ]

example (i : Fin 3) : affinePowerCoefficients 2 5 testQuadratic i =
    (![3, 9, 9] : Fin 3 → ℚ) i := by
  fin_cases i <;> norm_num [affinePowerCoefficients, testQuadratic, Fin.sum_univ_succ]

example : powerToBernstein (![0,0,1,0] : Fin 4 → ℚ) 2 = 1/3 := by
  norm_num [powerToBernstein, Fin.sum_univ_succ]

/-- Omitting the degree-elevation binomial denominator would give the false value one. -/
example : powerToBernstein (![0,0,1,0] : Fin 4 → ℚ) 2 ≠ 1 := by
  norm_num [powerToBernstein, Fin.sum_univ_succ]

example (c : ℚ) : powerToBernstein (fun _ : Fin 1 => c) 0 = c := by
  simp [powerToBernstein]

/-- The lower bound includes both interval endpoints. -/
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1/2 : ℝ) ≤ rationalEval (fun _ : Fin 1 => x) (powerPolynomial testQuadratic) := by
  have hc : ∀ i, (1/2 : ℚ) ≤ powerToBernstein (affinePowerCoefficients 0 1 testQuadratic) i := by
    intro i
    fin_cases i <;> norm_num [powerToBernstein, affinePowerCoefficients,
      testQuadratic, Fin.sum_univ_succ]
  have h := powerPolynomial_box_lower_bound 0 1 testQuadratic (1/2) (by norm_num) hc x
    (by simpa using hx)
  norm_num at h
  exact h

#print axioms DittertRybin.Certificates.powerPolynomial_eq_tensorPolynomial
#print axioms DittertRybin.Certificates.affineNormalize_powerPolynomial
#print axioms DittertRybin.Certificates.powerPolynomial_box_lower_bound
