import DR.Rectangular.FourRowFinitePowerAlgebra

/-! Exact multiplication by the affine ordinary-column weights in the row-kernel checks. -/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

def fourRowFinitePowerExtend (p : Fin 8 → ℚ) (d : ℕ) : ℚ :=
  if h : d < 8 then p ⟨d,h⟩ else 0

def fourRowFinitePowerLinear (b c : ℚ) (p : Fin 8 → ℚ) (d : Fin 9) : ℚ :=
  b*fourRowFinitePowerExtend p d.val+
    if d.val = 0 then 0 else c*fourRowFinitePowerExtend p (d.val-1)

theorem fourRowFinitePowerLinear_polynomial (b c : ℚ) (p : Fin 8 → ℚ) :
    powerPolynomial (fourRowFinitePowerLinear b c p) =
      (C b+C c*X 0)*powerPolynomial p := by
  apply MvPolynomial.funext
  intro x
  simp [fourRowFinitePowerLinear, fourRowFinitePowerExtend, powerPolynomial, Fin.sum_univ_succ]
  ring

theorem fourRowFinitePower_sum {ι : Type*} [Fintype ι] {d : ℕ} (p : ι → Fin (d+1) → ℚ) :
    powerPolynomial (fun k => ∑ i, p i k) = ∑ i, powerPolynomial (p i) := by
  simp only [powerPolynomial, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem fourRowFinitePowerLinear_eval (b c : ℚ) (p : Fin 8 → ℚ) (u : ℝ) :
    rationalEval (fun _ => u) (powerPolynomial (fourRowFinitePowerLinear b c p)) =
      ((b : ℝ)+(c : ℝ)*u)*rationalEval (fun _ => u) (powerPolynomial p) := by
  rw [fourRowFinitePowerLinear_polynomial]
  simp only [rationalEval, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, Rat.coe_castHom]

end
end DittertRybin
