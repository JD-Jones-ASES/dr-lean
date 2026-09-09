import DR.Certificates.PrincipalKernel
import Mathlib.Tactic.FinCases

open scoped BigOperators
open DittertRybin.Certificates

private def testQ : Matrix (Fin 2) (Fin 2) ℝ := ![![4,-2],![-2,1]]

private theorem testQ_symm : testQ.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem testQ_kernel : testQ.mulVec (![1,2] : Fin 2 → ℝ) = 0 := by
  ext i
  fin_cases i <;> norm_num [testQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem testQ_principal :
    (testQ.submatrix Fin.castSucc Fin.castSucc).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_iff_isSymm.mpr (testQ_symm.submatrix Fin.castSucc)
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    have hs := mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero hx0)
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, star_trivial]
    change 0 < x 0 * (4 * x 0)
    nlinarith only [hs]

-- The kernel vector need not be constant; the omitted component is exactly two.
example : testQ.PosSemidef ∧ ∀ x : Fin 2 → ℝ,
    quadraticValue testQ x = 0 ↔ ∃ t : ℝ, ∀ i, x i = t * (![1,2] : Fin 2 → ℝ) i :=
  principal_kernel_criterion testQ testQ_symm ![1,2] testQ_kernel (Equiv.refl _)
    (by change (2 : ℝ) ≠ 0; norm_num) testQ_principal

-- Substituting the all-ones vector would invalidate the actual kernel check.
example : testQ.mulVec (![1,1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [testQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0

-- The zero vector is included in the exact quadratic kernel.
example : quadraticValue testQ (0 : Fin 2 → ℝ) = 0 := by simp [quadraticValue]

#print axioms mulVec_kernel_submatrix_equiv
#print axioms principal_kernel_criterion
