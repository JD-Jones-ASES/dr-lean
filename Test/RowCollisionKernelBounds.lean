import DR.Endpoint.RowCollisionKernelBounds
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- Three independent uniform rows on 128 columns give a genuine normalized
-- law to which the full localized criterion applies.
private noncomputable def X : Board 3 128 := fun _ _ => 1/128
private theorem hX : ∀ i j,0≤X i j := by intro i j; norm_num [X]
private theorem hs : ∀ i,rowSum X i=1 := by intro i; norm_num [X,rowSum]
private theorem hc : ∀ j,colSum X j≤(3/128:ℝ) := by intro j; norm_num [X,colSum]

private theorem allBounds :
    0<rowAvoidance X ∧
    (∑ i,rowLocalizedDoubletonLoad X i)/(3:ℝ)≤1/4 ∧
    (∑ i,(rowLocalizedDoubletonLoad X i-
      (∑ j,rowLocalizedDoubletonLoad X j)/(3:ℝ))^2)≤1/64 ∧
    ∀ i,rowLocalizedDeficitTwoLoad X i≤1/4 := rowCollision_localized_kernel_bounds (by decide : 1≤3)
  X hX hs (3/128) (by norm_num) hc (by norm_num)

example : 0<rowAvoidance X := allBounds.1
example : (∑ i,rowLocalizedDoubletonLoad X i)/(3:ℝ)≤1/4 := allBounds.2.1
example : (∑ i,(rowLocalizedDoubletonLoad X i-
    (∑ j,rowLocalizedDoubletonLoad X j)/(3:ℝ))^2)≤1/64 := allBounds.2.2.1
example (i : Fin 3) : rowLocalizedDeficitTwoLoad X i≤1/4 := allBounds.2.2.2 i

-- A pointwise cap alone cannot replace the dimension-scaled squared cap.
example : ¬((16:ℝ)*(1/16)^2≤1/256) := by norm_num

-- Arbitrary nonnegative normalized rows, including zero cells, remain in the
-- production theorem's scope; no positive-cell premise occurs.
example {m n : ℕ} (hm : 1≤m) (Y : Board m n) (hY : ∀ i j,0≤Y i j)
    (hy : ∀ i,rowSum Y i=1) (C : ℝ) (hC0 : 0≤C)
    (hcap : ∀ j,colSum Y j≤C) (hC : (m:ℝ)*C^2≤1/256) :
    0<rowAvoidance Y := (rowCollision_localized_kernel_bounds hm Y hY hy C hC0 hcap hC).1

#print axioms rowCollision_localized_kernel_bounds
end DittertRybin.Tests
