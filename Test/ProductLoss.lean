import DR.Square.ProductLoss
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Boundary and mutation controls for actual minor product loss. -/
namespace DittertRybin.Tests
open scoped BigOperators

example : (1:ℝ)-(∑ _i ∈ (∅:Finset (Fin 1)), (0:ℝ)) ≤
    ∏ _i ∈ (∅:Finset (Fin 1)), (1-(0:ℝ)) :=
  one_sub_sum_le_product_one_sub ∅ (fun _ => 0) (by simp) (by simp)

-- A complete loss of one original positive factor is allowed.
example : (∏ _i : Fin 1, (2:ℝ)) * (1-∑ _i : Fin 1, (2:ℝ)/2) ≤
    ∏ _i : Fin 1, ((2:ℝ)-2) :=
  product_loss_lower Finset.univ (fun _ => 2) (fun _ => 2)
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)

-- Negative losses would invalidate the product-loss assertion.
example : ¬ ((1:ℝ)-((-1)+1/2) ≤ (1-(-1))*(1-1/2)) := by norm_num

-- Factors above one would invalidate the shared-deficit assertion.
example : ¬ ((2:ℝ)+2-1/5 ≤ (9/10)*2+(9/10)*2) := by norm_num

#print axioms one_sub_sum_le_product_one_sub
#print axioms product_loss_lower
#print axioms product_loss_lower_common
#print axioms weighted_factors_shared_deficit

end DittertRybin.Tests
