import DR.Certificates.FiniteK4FixedCases.M5S0
import DR.Certificates.FiniteK4FixedCases.M5S9

/-! Actual fixed-board pilot soundness and a weighted-kernel mutation control. -/
namespace DittertRybin.Certificates
open scoped BigOperators

example : ((finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 0).map
    (fun q : ℚ => (q : ℝ))).PosDef :=
  FiniteK4FixedCases.M5S0.principalGram.strictValid_posDef _
    FiniteK4FixedCases.M5S0.principal_valid
example : ((finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 9).map
    (fun q : ℚ => (q : ℝ))).PosDef :=
  FiniteK4FixedCases.M5S9.principalGram.strictValid_posDef _
    FiniteK4FixedCases.M5S9.principal_valid

-- The last aggregate coordinate has weight R*C=16; replacing it by1 fails.
example : ¬ (∀ i : Fin 4, (∑ j : Fin 4,
    finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 0 i j *
      (if j = 3 then 1 else finiteK4FixedWeight 5 5 0 j : ℚ)) = 0) := by
  decide +kernel

#print axioms FiniteK4FixedCases.M5S0.full_kernel
#print axioms FiniteK4FixedCases.M5S0.principal_valid
#print axioms FiniteK4FixedCases.M5S0.row_valid
#print axioms FiniteK4FixedCases.M5S0.column_valid
#print axioms FiniteK4FixedCases.M5S0.interaction_valid
#print axioms FiniteK4FixedCases.M5S9.full_kernel
#print axioms FiniteK4FixedCases.M5S9.principal_valid
#print axioms FiniteK4FixedCases.M5S9.row_valid
#print axioms FiniteK4FixedCases.M5S9.column_valid
#print axioms FiniteK4FixedCases.M5S9.interaction_valid
end DittertRybin.Certificates
