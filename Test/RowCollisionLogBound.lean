import DR.Endpoint.RowCollisionLogBound
import Mathlib.Algebra.BigOperators.Fin

namespace DittertRybin.Tests
open scoped BigOperators

-- The scalar zero boundary and an actual positive probability.
example : -Real.log (1-(0:ℝ)) ≤ 0/(1-0) :=
  neg_log_one_sub_le_div 0 (by norm_num)
example : -Real.log (3/4:ℝ) ≤ 1/3 := by
  have h := neg_log_one_sub_le_div (1/4) (by norm_num)
  norm_num at h
  exact h

-- Omitting the logarithmic denominator is false already for one event.
example : ¬(-Real.log (3/4:ℝ) ≤ 1/4) := by
  have h := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num)
    (show (3/4:ℝ) ≠ 1 by norm_num)
  linarith

-- Two zero parameters and one positive parameter use the same finite theorem.
example : -Real.log (∏ e : Fin 3, (1-(![(0:ℝ),1/4,0] e))) ≤ 1/3 := by
  have h := neg_log_product_one_sub_le Finset.univ ![(0:ℝ),1/4,0] (1/4)
    (by norm_num) (by intro e he; fin_cases e <;> norm_num)
  norm_num [Fin.sum_univ_succ] at h
  exact h

-- The actual empty row law has no exceptional normalization case.
example : -Real.log (rowAvoidance (0 : Board 0 0)) ≤ rowCollisionIntensity (0 : Board 0 0) := by
  have h := neg_log_rowAvoidance_le (0 : Board 0 0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    0 (by norm_num) (by norm_num) (by intro i; exact Fin.elim0 i)
  simpa using h

-- The genuine functional admits total intensity above one; no D-smallness premise is required.
example {m n : ℕ} (X : Board m n) (hX : ∀ i j, 0 ≤ X i j)
    (hs : ∀ i, rowSum X i=1) (hload : ∀ i, rowCollisionLoad X i ≤ 1/8) :
    Real.exp (-(8/3)*rowCollisionIntensity X) ≤ rowAvoidance X := by
  have h := exp_neg_collisionIntensity_le_rowAvoidance X hX hs (1/8)
    (by norm_num) (by norm_num) hload
  convert h using 1
  congr 1
  ring

#print axioms neg_log_one_sub_le_div
#print axioms neg_log_product_one_sub_le
#print axioms neg_log_rowAvoidance_le
#print axioms exp_neg_collisionIntensity_le_rowAvoidance

end DittertRybin.Tests
