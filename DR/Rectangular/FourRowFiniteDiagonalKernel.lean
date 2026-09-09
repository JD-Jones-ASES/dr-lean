import DR.Rectangular.FourRowFiniteDiagonalCache

/-! Exact reuse of the checked diagonal role table in the full kernel arithmetic. -/

namespace DittertRybin
open scoped BigOperators
noncomputable section

def fourRowFiniteDiagonalRole (i j c d : ℕ) : Fin 391 :=
  if i < 4 ∧ j < 4 ∧ c < 5 ∧ d < 5 then fourRowFiniteDiagonalRoleIndex i j c d
  else fourRowFiniteRoleLookup (fourRowFiniteSeedFastKey 9 (i,c) (j,d))

theorem fourRowFiniteDiagonalRole_eq (i j c d : ℕ) :
    fourRowFiniteDiagonalRole i j c d =
      fourRowFiniteRoleLookup (fourRowFiniteSeedFastKey 9 (i,c) (j,d)) := by
  unfold fourRowFiniteDiagonalRole
  split_ifs with h
  · exact fourRowFiniteDiagonalRoleIndex_correct ⟨i,h.1⟩ ⟨j,h.2.1⟩
      ⟨c,h.2.2.1⟩ ⟨d,h.2.2.2⟩
  · rfl

def fourRowFiniteDiagonalFullPower (h : Fin 391 → Fin 5 → ℚ) (a : ℕ)
    (i j : Fin (fourRowFiniteSeedFullSize 9)) : Fin 8 → ℚ :=
  fourRowFiniteColumnPower a 2
    (fun c d => h (fourRowFiniteDiagonalRole
      ((fourRowFiniteSeedPoint 9 i.val).1) ((fourRowFiniteSeedPoint 9 j.val).1) c d))
    (fourRowFiniteSeedPoint 9 i.val).2 (fourRowFiniteSeedPoint 9 j.val).2

theorem fourRowFiniteDiagonalFullPower_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ)
    (i j : Fin (fourRowFiniteSeedFullSize 9)) :
    fourRowFiniteDiagonalFullPower h a i j = fourRowFiniteSeedFullPowerOneRow h a 9 i j := by
  simp only [fourRowFiniteDiagonalFullPower,fourRowFiniteDiagonalRole_eq]
  rfl

def fourRowFiniteDiagonalKernelPower (h : Fin 391 → Fin 5 → ℚ) (a : ℕ)
    (i : Fin (fourRowFiniteSeedFullSize 9)) (d : Fin 9) : ℚ :=
  ∑ j : Fin (fourRowFiniteSeedFullSize 9),
    fourRowFinitePowerLinear (fourRowFiniteSeedAffineConstant a 9 j.val)
      (fourRowFiniteSeedAffineLinear 9 j.val) (fourRowFiniteDiagonalFullPower h a i j) d

theorem fourRowFiniteDiagonalKernelPower_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ)
    (i : Fin (fourRowFiniteSeedFullSize 9)) :
    fourRowFiniteDiagonalKernelPower h a i = fourRowFiniteSeedKernelPowerOneRow h a 9 i := by
  funext d
  simp only [fourRowFiniteDiagonalKernelPower,fourRowFiniteSeedKernelPowerOneRow,
    fourRowFiniteDiagonalFullPower_eq]

end
end DittertRybin
