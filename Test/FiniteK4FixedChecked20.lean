import DR.Certificates.FiniteK4FixedChecked20

/-! Closed finite all-seed matrix interfaces and meaningful signed/kernel controls. -/
namespace DittertRybin.Certificates
open scoped BigOperators

example (s : Fin 10) :
    (finiteK4FixedFullMatrix (fun k => (finiteK4Fixed20Coefficient k : ℝ)) 20 20 s).mulVec
      (finiteK4FixedWeight 20 20 s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 :=
  finiteK4Fixed20_full_kernel_real s

-- This is strict positivity for every nonzero real principal-block vector.
example (s : Fin 10) (x : Fin (fourRowFiniteSeedFullSize s-1) → ℝ) (hx : x ≠ 0) :
    0 < star x ⬝ᵥ ((finiteK4FixedPrincipalMatrix
      (fun k => (finiteK4Fixed20Coefficient k : ℝ)) 20 20 s).mulVec x) :=
  (finiteK4Fixed20_principal_posDef s).dotProduct_mulVec_pos hx

-- A negative literal coefficient is retained by the actual PSD certificate.
example : finiteK4Fixed20Coefficient 406 < 0 := by decide +kernel

-- The full compressed kernel requires multiplicities; the all-one vector fails.
example : ¬ (∀ i : Fin 4, (∑ j : Fin 4,
    finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 0 i j) = 0) := by
  decide +kernel

#print axioms finiteK4Fixed20_full_kernel
#print axioms finiteK4Fixed20_full_kernel_real
#print axioms finiteK4Fixed20_principal_posDef
#print axioms finiteK4Fixed20_row_posDef
#print axioms finiteK4Fixed20_column_posDef
#print axioms finiteK4Fixed20_interaction_posDef
end DittertRybin.Certificates
