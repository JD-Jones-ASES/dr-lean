import DR.Rectangular.FourRowFiniteCertifiedKernels

namespace DittertRybin
noncomputable section

example : (fourRowFiniteSeedFullMatrix 9 5 (fourRowFinite5RoleValue 1)).mulVec
    (fun j => fourRowFiniteSeedWeight 9 5 j.val) = 0 := by
  simpa using fourRowFinite5_full_kernel 9 1 (by norm_num)

example : (fourRowFiniteSeedFullMatrix 0 500 (fourRowFinite50RoleValue (1/10))).mulVec
    (fun j => fourRowFiniteSeedWeight 0 500 j.val) = 0 := by
  convert fourRowFinite50_full_kernel 0 (1/10) (by norm_num) using 1
  norm_num

-- The ordinary-column multiplicity survives even when there is exactly one ordinary row.
example : fourRowFiniteSeedWeight 9 5 0 = 1 ∧ fourRowFiniteSeedWeight 9 5 3 = 2 ∧
    fourRowFiniteSeedWeight 9 5 12 = 1 ∧ fourRowFiniteSeedWeight 9 5 15 = 2 := by
  have hr : fourRowFiniteSeedRows 9 = 3 := rfl
  have hc : fourRowFiniteSeedColumns 9 = 3 := rfl
  norm_num [fourRowFiniteSeedWeight,fourRowFiniteSeedRowWeight,fourRowFiniteSeedPoint,hr,hc]

example : fourRowFiniteSeedWeight 9 5 15 ≠ 1 := by
  have hr : fourRowFiniteSeedRows 9 = 3 := rfl
  have hc : fourRowFiniteSeedColumns 9 = 3 := rfl
  norm_num [fourRowFiniteSeedWeight,fourRowFiniteSeedRowWeight,fourRowFiniteSeedPoint,hr,hc]

example (s : Fin 10) (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) (j : ℕ) :
    0 < fourRowFiniteSeedWeight s (5/u) j :=
  fourRowFiniteSeedWeight_parameter_pos s (a := 5) (by decide) (by linarith) hu.2 j

example : ∀ s : Fin 10,
    fourRowFiniteSeedPoint s (fourRowFiniteSeedFullSize s-1) =
      (fourRowFiniteSeedRows s,fourRowFiniteSeedColumns s) := by
  decide +kernel

-- Equal and distinct ordinary columns stay different in the cached role table.
example : fourRowFiniteDiagonalRoleIndex 3 3 3 3 ≠
    fourRowFiniteDiagonalRoleIndex 3 3 3 4 := by
  decide +kernel

-- The total cached evaluator retains the actual definition outside its finite cache.
example : fourRowFiniteDiagonalRole 7 9 11 13 =
    fourRowFiniteRoleLookup (fourRowFiniteSeedFastKey 9 (7,11) (9,13)) :=
  fourRowFiniteDiagonalRole_eq 7 9 11 13

example (h : Fin 391 → Fin 5 → ℚ) (a : ℕ)
    (i j : Fin (fourRowFiniteSeedFullSize 9)) :
    fourRowFiniteSeedFullPowerOneRow h a 9 i j = fourRowFiniteSeedFullPowerFast h a 9 i j :=
  fourRowFiniteSeedFullPowerOneRow_eq h a 9 (by rfl) i j

#print axioms fourRowFinitePowerLinear_polynomial
#print axioms fourRowFiniteSeedKernelPower_eval
#print axioms fourRowFinite5_full_kernel_coefficients
#print axioms fourRowFinite50_full_kernel_coefficients
#print axioms fourRowFinite5_full_kernel
#print axioms fourRowFinite50_full_kernel
#print axioms fourRowFiniteSeedWeight_parameter_pos
#print axioms fourRowFiniteDiagonalRoleIndex_correct
#print axioms fourRowFiniteDiagonalKernelPower_eq
#print axioms fourRowFiniteSeedFullPowerOneRow_eq

end
end DittertRybin
