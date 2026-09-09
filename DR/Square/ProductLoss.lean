import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact finite product-loss inequalities for actual rows and columns of a minor. -/

namespace DittertRybin
open scoped BigOperators

theorem one_sub_sum_le_product_one_sub {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1) :
    1-∑ i ∈ s, z i ≤ ∏ i ∈ s, (1-z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hza := hz a (Finset.mem_insert_self _ _)
    have hza1 := hz1 a (Finset.mem_insert_self _ _)
    have hzs (i) (hi : i ∈ s) := hz i (Finset.mem_insert_of_mem hi)
    have hz1s (i) (hi : i ∈ s) := hz1 i (Finset.mem_insert_of_mem hi)
    have hh := mul_le_mul_of_nonneg_left (ih hzs hz1s) (sub_nonneg.mpr hza1)
    have hsum : 0 ≤ ∑ i ∈ s, z i := Finset.sum_nonneg hzs
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith

/-- The losses may remove an entire entry; only the original factors must be positive. -/
theorem product_loss_lower {ι : Type*} (s : Finset ι) (x z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hzx : ∀ i ∈ s, z i ≤ x i) :
    (∏ i ∈ s, x i) * (1-∑ i ∈ s, z i / x i) ≤ ∏ i ∈ s, (x i-z i) := by
  have hh := one_sub_sum_le_product_one_sub s (fun i => z i/x i)
    (fun i hi => div_nonneg (hz i hi) (hx i hi).le)
    (fun i hi => (div_le_one (hx i hi)).mpr (hzx i hi))
  have hp : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg fun i hi => (hx i hi).le
  have heq : (∏ i ∈ s, x i) * (∏ i ∈ s, (1-z i/x i)) = ∏ i ∈ s, (x i-z i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    field_simp [(hx i hi).ne']
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hh hp

/-- A common positive original marginal converts the weighted loss to total lost mass. -/
theorem product_loss_lower_common {ι : Type*} (s : Finset ι) (x z : ι → ℝ)
    (L : ℝ) (hL : 0 < L) (hx : ∀ i ∈ s, L ≤ x i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hzx : ∀ i ∈ s, z i ≤ x i) :
    (∏ i ∈ s, x i) * (1-(∑ i ∈ s, z i)/L) ≤ ∏ i ∈ s, (x i-z i) := by
  have hxp (i) (hi : i ∈ s) := hL.trans_le (hx i hi)
  have hloss : (∑ i ∈ s, z i / x i) ≤ (∑ i ∈ s, z i)/L := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => div_le_div_of_nonneg_left (hz i hi) hL (hx i hi)
  have hp : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg fun i hi => (hxp i hi).le
  exact (mul_le_mul_of_nonneg_left (by linarith :
    1-(∑ i ∈ s, z i)/L ≤ 1-∑ i ∈ s, z i/x i) hp).trans
    (product_loss_lower s x z hxp hz hzx)

/-- Two factors bounded by one lose at most the shared marginal-product budget. -/
theorem weighted_factors_shared_deficit {R C a b delta : ℝ}
    (hR : R ≤ 1) (hC : C ≤ 1) (ha : a ≤ 1) (hb : b ≤ 1)
    (hbudget : (1-R)+(1-C) ≤ delta) : a+b-delta ≤ R*a+C*b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr ha),
    mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hb)]

end DittertRybin
