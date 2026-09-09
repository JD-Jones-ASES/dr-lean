import DR.Rectangular.FourRowFiniteData5Block32Physical
import DR.Rectangular.FourRowFiniteData50Block32Physical

namespace DittertRybin
open Certificates
noncomputable section

-- These are the actual numerator-weighted principal block matrices, at both source boundaries.
example : (fourRowFinite5Block32ActualEntry 1).PosDef :=
  fourRowFinite5Block32_actualEntry_posDef 1 (by norm_num)

example : (fourRowFinite5Block32ActualEntry (1/10)).PosDef :=
  fourRowFinite5Block32_actualEntry_posDef (1/10) (by norm_num)

example : (fourRowFinite50Block32ActualEntry 1).PosDef :=
  fourRowFinite50Block32_actualEntry_posDef 1 (by norm_num)

example : (fourRowFinite50Block32ActualEntry (1/10)).PosDef :=
  fourRowFinite50Block32_actualEntry_posDef (1/10) (by norm_num)

-- A unit mutation of a stored constant coefficient cannot pass the actual-formula gate.
example : fourRowFinite5Block32Power 0 0 0+1 ≠
    fourRowFinitePowerPad (fourRowFinite5Block32ActualPower 0 0) 0 := by
  rw [fourRowFinite5Block32_power_actual]
  linarith

example (i j : Fin 15) : fourRowFinite50Block32Power i j 8 = 0 ∧
    fourRowFinite50Block32Power i j 9 = 0 := by
  simp only [fourRowFinite50Block32_power_actual, fourRowFinitePowerPad]
  norm_num

#print axioms fourRowFinite5Block32_power_actual
#print axioms fourRowFinite50Block32_power_actual
#print axioms fourRowFinite5Block32_polynomial_actual
#print axioms fourRowFinite50Block32_polynomial_actual
#print axioms fourRowFinite5Block32_actualEntry_clear
#print axioms fourRowFinite50Block32_actualEntry_clear
#print axioms fourRowFinite5Block32_actualEntry_posDef
#print axioms fourRowFinite50Block32_actualEntry_posDef

end
end DittertRybin
