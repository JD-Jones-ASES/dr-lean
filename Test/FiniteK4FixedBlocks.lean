import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData

/-! Persistent rational-sector, cast and exact-count boundary controls. -/
namespace DittertRybin.Certificates

private def boundaryPair : OrdinaryPair (Fin 1) → ℚ
  | .same => 7
  | .different => -3
  | _ => 0

example : finiteK4FixedAverage (1 : ℚ) boundaryPair (.inr ()) (.inr ()) = 7 := by
  decide +kernel
-- Zero-count arithmetic is defined; no physical PSD conclusion is asserted.
example : finiteK4FixedAverage (0 : ℚ) boundaryPair (.inr ()) (.inr ()) = -3 := by
  decide +kernel
example : finiteK4FixedAverage (2 : ℚ) boundaryPair (.inr ()) (.inr ()) = 2 := by
  decide +kernel
example : (finiteK4FixedWeight 5 5 0 (0 : Fin 4) : ℚ) = 1 := by decide +kernel
example : (finiteK4FixedWeight 5 5 0 (1 : Fin 4) : ℚ) = 4 := by decide +kernel
example : (finiteK4FixedWeight 5 5 0 (2 : Fin 4) : ℚ) = 4 := by decide +kernel
example : (finiteK4FixedWeight 5 5 0 (3 : Fin 4) : ℚ) = 16 := by decide +kernel
example : (finiteK4FixedWeight 20 20 9 (15 : Fin 16) : ℚ) = 289 := by decide +kernel
example : finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 0 (0 : Fin 4) (0 : Fin 4) = 5424/15625 := by
  decide +kernel
example : finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 0 (3 : Fin 4) (3 : Fin 4) = 8581/125000 := by
  decide +kernel
example : finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 0 0 0 = 130603/93750 := by
  decide +kernel
example : (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 9).map
    (fun q : ℚ => (q : ℝ)) =
    finiteK4FixedFullMatrix (fun i => (finiteK4Fixed20Coefficient i : ℝ)) 20 20 9 :=
  finiteK4FixedFullMatrix_cast _ _ _ _

#print axioms finiteK4FixedRoleLookup_key
#print axioms finiteK4FixedFullMatrix_cast
#print axioms finiteK4FixedPrincipalMatrix_cast
#print axioms finiteK4FixedRowMatrix_cast
#print axioms finiteK4FixedColumnMatrix_cast
#print axioms finiteK4FixedInteractionMatrix_cast
#print axioms finiteK4FixedFullMatrix_reindex
#print axioms finiteK4FixedWeight_reindex
end DittertRybin.Certificates
