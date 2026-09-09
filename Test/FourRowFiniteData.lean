import DR.Rectangular.FourRowFiniteData5Identities
import DR.Rectangular.FourRowFiniteData50Identities
import DR.Rectangular.FourRowFiniteLinearEvaluation
import DR.Rectangular.FourRowFiniteData5Block32Transform
import DR.Rectangular.FourRowFiniteData50Block32Transform

namespace DittertRybin
open Certificates
noncomputable section

example : fourRowFiniteFamilyNumerator5 0 0 = 0 := by decide +kernel
example : fourRowFiniteBernsteinNine 0 1 = (1 : ℚ)/10 := by decide +kernel

-- A mutation of the first role's constant coefficient is rejected by the true identity gate.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
example : ¬ (fourRowFiniteCoefficientRows 0).Valid 5
    (fun i d => if i = 0 ∧ d = 0 then fourRowFiniteFamilyNumerator5 i d+1
      else fourRowFiniteFamilyNumerator5 i d) := by
  decide +kernel

example (e : Fin 84) (u : ℝ) :
    ((fourRowFiniteCoefficientRows e).terms.map
      (fun t => (t.2 : ℝ)*fourRowFiniteNumeratorValue fourRowFiniteFamilyNumerator5 t.1 u)).sum =
      u*((fourRowFiniteCoefficientRows e).multiplicity*
        (1-87/(16*5)*u+319/(32*5^2)*u^2-87/(16*5^3)*u^3)-
          (fourRowFiniteCoefficientRows e).successes) :=
  (fourRowFinite5_coefficient_identities e).eval _ _ _ u

-- The last coefficient is included in the six-coefficient affine kernel check.
example (e : Fin 65) :
    fourRowFiniteKernelValid (fourRowFiniteKernelRows e) 50 fourRowFiniteFamilyNumerator50 :=
  fourRowFinite50_kernel_identities e

example (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteMatrixPolynomial (fun k i j => fourRowFinite5Block32Power i j k) u).PosDef :=
  fourRowFinite5Block32Polynomial_posDef u hu

example :
    (fourRowFiniteMatrixPolynomial (fun k i j => fourRowFinite50Block32Power i j k) (1/10)).PosDef :=
  fourRowFinite50Block32Polynomial_posDef _ (by norm_num)

example :
    (fourRowFiniteMatrixPolynomial (fun k i j => fourRowFinite50Block32Power i j k) 1).PosDef :=
  fourRowFinite50Block32Polynomial_posDef _ (by norm_num)

#print axioms fourRowFinite5_coefficient_identities
#print axioms fourRowFinite5_kernel_identities
#print axioms fourRowFinite50_coefficient_identities
#print axioms fourRowFinite50_kernel_identities
#print axioms FourRowFiniteCoefficientRow.Valid.eval
#print axioms fourRowFiniteKernelValid.eval_div
#print axioms fourRowFinite5Block32Polynomial_posDef
#print axioms fourRowFinite50Block32Polynomial_posDef

end
end DittertRybin
