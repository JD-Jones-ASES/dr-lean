import DR.Rectangular.FourRowFiniteSeeds
import DR.Rectangular.FourRowFinitePowerBlocks
import DR.Rectangular.FourRowFiniteKernelPower
import DR.Rectangular.FourRowFiniteFamilyPolynomial

/-!
# Actual full compressed row-kernel expressions

Multiplying the ordinary-column weights by u gives the affine weights
u and a-c*u. The resulting row polynomial has degree at most eight.
The checked expression includes the omitted principal coordinate.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

def fourRowFiniteSeedRowWeight (s : Fin 10) (j : ℕ) : ℚ :=
  if (fourRowFiniteSeedPoint s j).1 = fourRowFiniteSeedRows s then
    4-(fourRowFiniteSeedRows s : ℚ) else 1

def fourRowFiniteSeedWeight (s : Fin 10) (N : ℝ) (j : ℕ) : ℝ :=
  (fourRowFiniteSeedRowWeight s j : ℝ)*
    if (fourRowFiniteSeedPoint s j).2 = fourRowFiniteSeedColumns s then
      N-fourRowFiniteSeedColumns s else 1

def fourRowFiniteSeedAffineConstant (a : ℕ) (s : Fin 10) (j : ℕ) : ℚ :=
  if (fourRowFiniteSeedPoint s j).2 = fourRowFiniteSeedColumns s then
    fourRowFiniteSeedRowWeight s j*a else 0

def fourRowFiniteSeedAffineLinear (s : Fin 10) (j : ℕ) : ℚ :=
  if (fourRowFiniteSeedPoint s j).2 = fourRowFiniteSeedColumns s then
    -(fourRowFiniteSeedRowWeight s j)*(fourRowFiniteSeedColumns s) else
      fourRowFiniteSeedRowWeight s j

def fourRowFiniteSeedFullPower (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i j : Fin (fourRowFiniteSeedFullSize s)) : Fin 8 → ℚ :=
  fourRowFiniteTrivialPower (fourRowFiniteSeedRows s)
    ⟨fourRowFiniteSeedColumns s-1, by have := (fourRowFiniteSeed_counts s).2.2.2; omega⟩ a
    (fun key => h (fourRowFiniteRoleLookup key)) (fourRowFiniteSeedMark s)
    (fourRowFiniteSeedPoint s i.val) (fourRowFiniteSeedPoint s j.val)

def fourRowFiniteSeedKernelPower (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) (d : Fin 9) : ℚ :=
  ∑ j : Fin (fourRowFiniteSeedFullSize s),
    fourRowFinitePowerLinear (fourRowFiniteSeedAffineConstant a s j.val)
      (fourRowFiniteSeedAffineLinear s j.val) (fourRowFiniteSeedFullPower h a s i j) d

def fourRowFiniteSeedFullMatrix (s : Fin 10) (N : ℝ) (h : ℕ → ℝ) :
    Matrix (Fin (fourRowFiniteSeedFullSize s)) (Fin (fourRowFiniteSeedFullSize s)) ℝ :=
  fun i j => fourRowFiniteTrivialEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
    N h (fourRowFiniteSeedMark s) (fourRowFiniteSeedPoint s i.val) (fourRowFiniteSeedPoint s j.val)

theorem fourRowFiniteSeedAffine_eq (a : ℕ) (s : Fin 10) (j : ℕ) (u : ℝ) (hu : u ≠ 0) :
    (fourRowFiniteSeedAffineConstant a s j : ℝ)+(fourRowFiniteSeedAffineLinear s j : ℝ)*u =
      u*fourRowFiniteSeedWeight s ((a : ℝ)/u) j := by
  unfold fourRowFiniteSeedAffineConstant fourRowFiniteSeedAffineLinear fourRowFiniteSeedWeight
  split_ifs <;> push_cast <;> field_simp <;> ring

theorem fourRowFiniteSeedKernelPower_polynomial (h : Fin 391 → Fin 5 → ℚ)
    (a : ℕ) (s : Fin 10) (i : Fin (fourRowFiniteSeedFullSize s)) :
    powerPolynomial (fourRowFiniteSeedKernelPower h a s i) =
      ∑ j : Fin (fourRowFiniteSeedFullSize s),
        (C (fourRowFiniteSeedAffineConstant a s j.val)+
          C (fourRowFiniteSeedAffineLinear s j.val)*X 0)*
            powerPolynomial (fourRowFiniteSeedFullPower h a s i j) := by
  unfold fourRowFiniteSeedKernelPower
  rw [fourRowFinitePower_sum]
  simp only [fourRowFinitePowerLinear_polynomial]

end
end DittertRybin
