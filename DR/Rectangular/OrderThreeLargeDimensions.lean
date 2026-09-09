import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact dimension ranges for the three-sample near-region scalar criterion. -/

namespace DittertRybin
noncomputable section

def orderThreeReciprocalCriterion (x y : ℝ) : ℝ :=
  (3 - 6*x - 6*y + 8*x*y) - 3/4 - 18*(x+y)/(9/2 - 12*x)

def orderThreeLargeCriterion (m n : ℝ) : ℝ :=
  (3 - 6/m - 6/n + 8/(m*n)) - 3/4 - 18*(1/m + 1/n)/(9/2 - 12/m)

theorem orderThreeLargeCriterion_eq_reciprocal (m n : ℝ) :
    orderThreeLargeCriterion m n = orderThreeReciprocalCriterion (1/m) (1/n) := by
  unfold orderThreeLargeCriterion orderThreeReciprocalCriterion
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The criterion improves as the larger dimension grows. -/
theorem orderThreeReciprocalCriterion_mono {x y z : ℝ} (hx : x ≤ 1/6)
    (hyz : y ≤ z) : orderThreeReciprocalCriterion x z ≤ orderThreeReciprocalCriterion x y := by
  have hd : 0 < 9/2 - 12*x := by linarith
  have hq : 18*(x+y)/(9/2 - 12*x) ≤ 18*(x+z)/(9/2 - 12*x) :=
    (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  have hh := mul_nonneg (sub_nonneg.mpr hyz) (show 0 ≤ 6 - 8*x by linarith)
  unfold orderThreeReciprocalCriterion
  nlinarith

/-- The exact uniform lower margin in the entire reciprocal triangle. -/
theorem orderThreeReciprocalCriterion_ge_tenth {x y : ℝ}
    (hyx : y ≤ x) (hx : x ≤ 1/10) :
    (43/1100 : ℝ) ≤ orderThreeReciprocalCriterion x y := by
  have hd : 0 < 9/2 - 12*x := by linarith
  have hq : 18*(x+y)/(9/2 - 12*x) ≤ 12/11 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hxy := mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ 6 - 8*x by linarith)
  have hc : 47/25 ≤ 3 - 6*x - 6*y + 8*x*y := by
    nlinarith [sq_nonneg (x - 1/10)]
  unfold orderThreeReciprocalCriterion
  linarith

theorem orderThreeLargeDimensions_ge_ten {m n : ℕ} (hm : 10 ≤ m) (hn : m ≤ n) :
    0 < (9/2 : ℝ) - 12/(m : ℝ) ∧ 0 < orderThreeLargeCriterion m n := by
  have hmR : (10 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (m : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by linarith
  have hx : 1/(m : ℝ) ≤ 1/10 := one_div_le_one_div_of_le (by norm_num) hmR
  have hyx : 1/(n : ℝ) ≤ 1/(m : ℝ) := one_div_le_one_div_of_le hm0 hnR
  have h := orderThreeReciprocalCriterion_ge_tenth hyx hx
  rw [← orderThreeLargeCriterion_eq_reciprocal] at h
  constructor
  · have he : 12/(m : ℝ) = 12*(1/(m : ℝ)) := by ring
    rw [he]
    linarith
  · linarith

/-- A rational reciprocal endpoint certifies every larger integer column dimension. -/
theorem orderThreeLargeDimensions_of_endpoint (m n₀ n : ℕ)
    (hm : 6 ≤ m) (hn₀ : 0 < n₀) (hn : n₀ ≤ n)
    (hbase : 0 < orderThreeReciprocalCriterion (1/(m : ℝ)) (1/(n₀ : ℝ))) :
    0 < (9/2 : ℝ) - 12/(m : ℝ) ∧ 0 < orderThreeLargeCriterion m n := by
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hn₀R : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1/(m : ℝ) ≤ 1/6 := one_div_le_one_div_of_le (by norm_num) hmR
  have hyz : 1/(n : ℝ) ≤ 1/(n₀ : ℝ) := one_div_le_one_div_of_le hn₀R hnR
  have h := orderThreeReciprocalCriterion_mono hx hyz
  constructor
  · have he : 12/(m : ℝ) = 12*(1/(m : ℝ)) := by ring
    rw [he]
    linarith
  · rw [orderThreeLargeCriterion_eq_reciprocal]
    exact hbase.trans_le h

theorem orderThreeLargeDimensions_six {n : ℕ} (hn : 238 ≤ n) :
    0 < (9/2 : ℝ) - 12/6 ∧ 0 < orderThreeLargeCriterion 6 n := by
  exact orderThreeLargeDimensions_of_endpoint 6 238 n (by decide) (by decide) hn
    (by norm_num [orderThreeReciprocalCriterion])

theorem orderThreeLargeDimensions_seven {n : ℕ} (hn : 25 ≤ n) :
    0 < (9/2 : ℝ) - 12/7 ∧ 0 < orderThreeLargeCriterion 7 n := by
  exact orderThreeLargeDimensions_of_endpoint 7 25 n (by decide) (by decide) hn
    (by norm_num [orderThreeReciprocalCriterion])

theorem orderThreeLargeDimensions_eight {n : ℕ} (hn : 15 ≤ n) :
    0 < (9/2 : ℝ) - 12/8 ∧ 0 < orderThreeLargeCriterion 8 n := by
  exact orderThreeLargeDimensions_of_endpoint 8 15 n (by decide) (by decide) hn
    (by norm_num [orderThreeReciprocalCriterion])

theorem orderThreeLargeDimensions_nine {n : ℕ} (hn : 12 ≤ n) :
    0 < (9/2 : ℝ) - 12/9 ∧ 0 < orderThreeLargeCriterion 9 n := by
  exact orderThreeLargeDimensions_of_endpoint 9 12 n (by decide) (by decide) hn
    (by norm_num [orderThreeReciprocalCriterion])

end
end DittertRybin
