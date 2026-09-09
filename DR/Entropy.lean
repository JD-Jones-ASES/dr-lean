import DR.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite entropy inequalities on the closed simplex

The convention `0 * log 0 = 0` is used explicitly. Jensen's inequality for
`x * log x` supplies the uniform entropy bound without an interior assumption;
Jensen for the exponential supplies the weighted geometric-mean bound even
when an observable is positive only on the support of its weights.
-/

open scoped BigOperators

namespace DittertRybin

/-- Entropy is maximized by the uniform distribution, including zero weights. -/
theorem neg_log_card_le_sum_mul_log {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    -Real.log d ≤ ∑ i, p i * Real.log (p i) := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hw : ∑ _i : Fin d, (d : ℝ)⁻¹ = 1 := by simp [ne_of_gt hd0]
  have h := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin d => (d : ℝ)⁻¹) (p := p)
    (fun _ _ => inv_nonneg.mpr hd0.le) hw (fun i _ => hp i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one] at h
  rw [Real.log_inv] at h
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hd0)).mp h

/-- The weighted geometric-mean inequality with positivity only on support. -/
theorem exp_sum_mul_log_le_sum_mul {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hx : ∀ i, 0 < w i → 0 < x i) :
    Real.exp (∑ i, w i * Real.log (x i)) ≤ ∑ i, w i * x i := by
  have h := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := w) (p := fun i => Real.log (x i))
    (fun i _ => hw i) hs (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  calc
    _ ≤ ∑ i, w i * Real.exp (Real.log (x i)) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_or_lt_of_le (hw i) with hi | hi
      · simp [← hi]
      · rw [Real.exp_log (hx i hi)]

end DittertRybin
