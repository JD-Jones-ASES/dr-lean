import DR.Certificates.FiniteK4FixedChecked5

/-! Closed finite all-seed matrix interfaces and meaningful signed/kernel controls. -/
namespace DittertRybin.Certificates
open scoped BigOperators

example (s : Fin 10) :
    (finiteK4FixedFullMatrix (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 5 s).mulVec
      (finiteK4FixedWeight 5 5 s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 :=
  finiteK4Fixed5_full_kernel_real s

-- This is strict positivity for every nonzero real principal-block vector.
example (s : Fin 10) (x : Fin (fourRowFiniteSeedFullSize s-1) → ℝ) (hx : x ≠ 0) :
    0 < star x ⬝ᵥ ((finiteK4FixedPrincipalMatrix
      (fun k => (finiteK4Fixed5Coefficient k : ℝ)) 5 5 s).mulVec x) :=
  (finiteK4Fixed5_principal_posDef s).dotProduct_mulVec_pos hx

-- A negative literal coefficient is retained by the actual PSD certificate.
example : finiteK4Fixed5Coefficient 406 < 0 := by decide +kernel

-- The full compressed kernel requires multiplicities; the all-one vector fails.
example : ¬ (∀ i : Fin 4, (∑ j : Fin 4,
    finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 0 i j) = 0) := by
  decide +kernel

#print axioms finiteK4Fixed5_full_kernel
#print axioms finiteK4Fixed5_full_kernel_real
#print axioms finiteK4Fixed5_principal_posDef
#print axioms finiteK4Fixed5_row_posDef
#print axioms finiteK4Fixed5_column_posDef
#print axioms finiteK4Fixed5_interaction_posDef

-- The cast identity itself retains zero-count and arbitrary signed inputs.
example (coeff : Fin 407 → ℚ) (s : Fin 10)
    (h : (finiteK4FixedFullMatrix coeff 0 1 s).mulVec
      (finiteK4FixedWeight 0 1 s : Fin (fourRowFiniteSeedFullSize s) → ℚ) = 0) :
    (finiteK4FixedFullMatrix (fun k => (coeff k : ℝ)) 0 1 s).mulVec
      (finiteK4FixedWeight 0 1 s : Fin (fourRowFiniteSeedFullSize s) → ℝ) = 0 :=
  finiteK4FixedFullMatrix_kernel_cast _ _ _ _ h

#print axioms finiteK4FixedFullMatrix_kernel_cast
end DittertRybin.Certificates
