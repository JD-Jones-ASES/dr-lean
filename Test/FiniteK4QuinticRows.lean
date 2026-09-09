import DR.Certificates.FiniteK4QuinticRows

namespace DittertRybin.Tests
open Certificates

-- The restricted equations are literal source rows, with all407 role indices
-- mapped from the exact391 four-row catalogue.
example : ∀ a : Fin 84,
    finiteK4QuinticMultiplicity.get (finiteK4QuinticFourRowEquations.get a) =
      (fourRowFiniteCoefficientRows a).multiplicity := fun a => (finiteK4QuinticFourRowRows a).2.1

-- Polynomial evaluation is signed; only the actual u denominator must be nonzero.
example (a : ℕ) (h : Fin 391 → Fin 5 → ℚ)
    (hv : ∀ e : Fin 84, (fourRowFiniteCoefficientRows e).Valid a h) :
    FiniteK4FourRowCoefficientEquations
      (1-87/(16*a)*(-1)+319/(32*a^2)*(-1)^2-87/(16*a^3)*(-1)^3)
      (fourRowFiniteUniversalCoefficient h (-1)) :=
  fourRowFiniteUniversalCoefficient_equations a h hv (-1) (by norm_num)

-- Setting u=0 destroys the equation even though Lean defines division by zero.
example (h : Fin 391 → Fin 5 → ℚ) :
    ¬ FiniteK4FourRowCoefficientEquations 1 (fourRowFiniteUniversalCoefficient h 0) := by
  intro he
  have hz := he 0
  have hm : finiteK4QuinticMultiplicity.get (finiteK4QuinticFourRowEquations.get 0)=1 := by decide +kernel
  have hs : finiteK4QuinticSuccesses.get (finiteK4QuinticFourRowEquations.get 0)=0 := by decide +kernel
  norm_num [finiteK4QuinticRowValue,fourRowFiniteUniversalCoefficient,hm,hs] at hz

#print axioms finiteK4QuinticRowTerms_padding
#print axioms finiteK4QuinticRowValue_list
#print axioms finiteK4QuinticFourRowRows
#print axioms finiteK4QuinticFourRowEquation_coverage
#print axioms FiniteK4FourRowCoefficientEquations.physical_row
#print axioms fourRowFiniteUniversalCoefficient_equations
end DittertRybin.Tests
