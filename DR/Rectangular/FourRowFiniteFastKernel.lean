import DR.Rectangular.FourRowFiniteSeedKernel
import DR.Rectangular.FourRowFiniteFastRole

/-! Proved evaluation acceleration for the same full weighted-kernel coefficients. -/

namespace DittertRybin
open scoped BigOperators
noncomputable section

def fourRowFiniteSeedFullPowerFast (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i j : Fin (fourRowFiniteSeedFullSize s)) : Fin 8 → ℚ :=
  fourRowFinitePowerAverage (fourRowFiniteSeedRows s) (4-fourRowFiniteSeedRows s)
    (fun r t => fourRowFiniteColumnPower a
      ⟨fourRowFiniteSeedColumns s-1, by have := (fourRowFiniteSeed_counts s).2.2.2; omega⟩
      (fun c d => h (fourRowFiniteRoleLookup (fourRowFiniteSeedFastKey s (r,c) (t,d))))
      (fourRowFiniteSeedPoint s i.val).2 (fourRowFiniteSeedPoint s j.val).2)
    (fourRowFiniteSeedPoint s i.val).1 (fourRowFiniteSeedPoint s j.val).1

theorem fourRowFiniteSeedFullPowerFast_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i j : Fin (fourRowFiniteSeedFullSize s)) :
    fourRowFiniteSeedFullPowerFast h a s i j = fourRowFiniteSeedFullPower h a s i j := by
  unfold fourRowFiniteSeedFullPowerFast fourRowFiniteSeedFullPower fourRowFiniteTrivialPower
  simp only [fourRowFiniteSeedFastKey_eq, fourRowFiniteRolePower]

def fourRowFiniteSeedKernelPowerFast (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) (d : Fin 9) : ℚ :=
  ∑ j : Fin (fourRowFiniteSeedFullSize s),
    fourRowFinitePowerLinear (fourRowFiniteSeedAffineConstant a s j.val)
      (fourRowFiniteSeedAffineLinear s j.val) (fourRowFiniteSeedFullPowerFast h a s i j) d

theorem fourRowFiniteSeedKernelPowerFast_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) :
    fourRowFiniteSeedKernelPowerFast h a s i = fourRowFiniteSeedKernelPower h a s i := by
  funext d
  simp only [fourRowFiniteSeedKernelPowerFast, fourRowFiniteSeedKernelPower,
    fourRowFiniteSeedFullPowerFast_eq]

end
end DittertRybin
