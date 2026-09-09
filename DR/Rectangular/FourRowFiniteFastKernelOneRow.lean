import DR.Rectangular.FourRowFiniteFastKernel

/-! The exact multiplicity-one simplification removes an absent ordinary-row
branch before evaluating a full weighted kernel. -/

namespace DittertRybin
open scoped BigOperators
noncomputable section

theorem fourRowFinitePowerAverage_one {d : ℕ} (first : ℕ)
    (f : ℕ → ℕ → Fin (d+1) → ℚ) (i j : ℕ) :
    fourRowFinitePowerAverage first 1 f i j = f i j := by
  funext k
  unfold fourRowFinitePowerAverage
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    simp
  · rfl

def fourRowFiniteSeedFullPowerOneRow (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i j : Fin (fourRowFiniteSeedFullSize s)) : Fin 8 → ℚ :=
  fourRowFiniteColumnPower a
    ⟨fourRowFiniteSeedColumns s-1, by have := (fourRowFiniteSeed_counts s).2.2.2; omega⟩
    (fun c d => h (fourRowFiniteRoleLookup (fourRowFiniteSeedFastKey s
      ((fourRowFiniteSeedPoint s i.val).1,c) ((fourRowFiniteSeedPoint s j.val).1,d))))
    (fourRowFiniteSeedPoint s i.val).2 (fourRowFiniteSeedPoint s j.val).2

theorem fourRowFiniteSeedFullPowerOneRow_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (hs : fourRowFiniteSeedRows s = 3) (i j : Fin (fourRowFiniteSeedFullSize s)) :
    fourRowFiniteSeedFullPowerOneRow h a s i j = fourRowFiniteSeedFullPowerFast h a s i j := by
  unfold fourRowFiniteSeedFullPowerFast
  have hc : (4 : ℚ)-fourRowFiniteSeedRows s = 1 := by rw [hs]; norm_num
  rw [hc,fourRowFinitePowerAverage_one]
  rfl

def fourRowFiniteSeedKernelPowerOneRow (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) (d : Fin 9) : ℚ :=
  ∑ j : Fin (fourRowFiniteSeedFullSize s),
    fourRowFinitePowerLinear (fourRowFiniteSeedAffineConstant a s j.val)
      (fourRowFiniteSeedAffineLinear s j.val) (fourRowFiniteSeedFullPowerOneRow h a s i j) d

theorem fourRowFiniteSeedKernelPowerOneRow_eq (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (hs : fourRowFiniteSeedRows s = 3) (i : Fin (fourRowFiniteSeedFullSize s)) :
    fourRowFiniteSeedKernelPowerOneRow h a s i = fourRowFiniteSeedKernelPowerFast h a s i := by
  funext d
  simp only [fourRowFiniteSeedKernelPowerOneRow,fourRowFiniteSeedKernelPowerFast,
    fourRowFiniteSeedFullPowerOneRow_eq h a s hs]

end
end DittertRybin
