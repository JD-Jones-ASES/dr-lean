import DR.Endpoint.UniformAvoidanceBound

namespace DittertRybin.Tests
open scoped BigOperators

-- The exact product includes both empty and single-draw sampling orders.
example : distinctUniformProbability 3 0 = 1 := by
  rw [distinctUniformProbability_eq_product (by decide) (by decide)]
  norm_num
example : distinctUniformProbability 3 1 = 1 := by
  rw [distinctUniformProbability_eq_product (by decide) (by decide)]
  norm_num
example : distinctUniformProbability 2 2 = 1/2 := by
  rw [distinctUniformProbability_eq_product (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]

-- Dropping the unordered-pair half factor gives a false probability bound.
example : ¬(distinctUniformProbability 2 2 ≤ Real.exp (-1)) := by
  have hp : distinctUniformProbability 2 2 = 1/2 := by
    rw [distinctUniformProbability_eq_product (by decide) (by decide)]
    norm_num [Finset.prod_range_succ]
  rw [hp,Real.exp_neg]
  have he : (2:ℝ)<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hi : (Real.exp 1)⁻¹ < (1/2:ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    linarith
  exact not_le.mpr hi

example : Real.exp (-10)<(1:ℝ)/16384 := exp_neg_ten_lt_inv16384

-- This is a nonempty accepted strip instance, proved without evaluating its
-- enormous factorial or sampling space.
example : distinctUniformProbability (2^39) (2^22)<(1:ℝ)/16384 := by
  apply distinctUniformProbability_small_of_twenty_mul_le <;> norm_num

-- The strip's upper edge is necessary for this uniform small-probability claim.
example : ¬(distinctUniformProbability 3 2<(1:ℝ)/16384) := by
  rw [distinctUniformProbability_eq_product (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]

#print axioms distinctUniformProbability_eq_product
#print axioms sum_range_real_eq_half
#print axioms distinctUniformProbability_le_exp
#print axioms exp_neg_ten_lt_inv16384
#print axioms distinctUniformProbability_small_of_twenty_mul_le
end DittertRybin.Tests
