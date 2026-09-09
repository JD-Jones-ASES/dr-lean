import DR.Certificates.FiniteK4FixedSeedEquations

/-! Persistent exact coefficient, signed-input and rejected-mutation controls.
No test assumes or claims matrix positivity from coefficient equations. -/
namespace DittertRybin.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

example : finiteK4Fixed5Coefficient 0 = 5424/15625 := by decide +kernel
example : finiteK4Fixed5Coefficient 406 = -61206/15625 := by decide +kernel
example : finiteK4Fixed20Coefficient 0 = 14805351/16000000 := by decide +kernel
example : finiteK4Fixed20Coefficient 406 = -3583947/8000000 := by decide +kernel

example : FiniteK4CoefficientEquations (5424/15625)
    (fun k => (finiteK4Fixed5Coefficient k : ℝ)) := finiteK4Fixed5_equations
example : FiniteK4CoefficientEquations (14805351/16000000)
    (fun k => (finiteK4Fixed20Coefficient k : ℝ)) := finiteK4Fixed20_equations

/-- Changing even the all-repeated coefficient fails an actual universal row. -/
example : ¬ FiniteK4RationalCoefficientEquations finiteK4Fixed5Alpha
    (Function.update finiteK4Fixed5Coefficient 0 (finiteK4Fixed5Coefficient 0 + 1)) := by
  decide +kernel
example : ¬ FiniteK4RationalCoefficientEquations finiteK4Fixed20Alpha
    (Function.update finiteK4Fixed20Coefficient 0 (finiteK4Fixed20Coefficient 0 - 1)) := by
  decide +kernel
example : ¬ FiniteK4RationalCoefficientEquations (finiteK4Fixed5Alpha + 1)
    finiteK4Fixed5Coefficient := by decide +kernel
example : ¬ FiniteK4RationalCoefficientEquations finiteK4Fixed20Alpha
    (fun _ => 0) := by decide +kernel

#print axioms FiniteK4RationalCoefficientEquations.cast
#print axioms finiteK4Fixed5_rational_equations
#print axioms finiteK4Fixed20_rational_equations
#print axioms finiteK4Fixed5_equations
#print axioms finiteK4Fixed20_equations
end DittertRybin.Certificates
