import DR.Endpoint.ArithmeticParameters

namespace DittertRybin.Tests

private theorem arithmetic_cut_256 :
    (22:ℝ)*256*Real.log 256≤(256:ℝ)*(256-1) := by
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : Real.log (256:ℝ)=8*Real.log 2 := by
    rw [show (256:ℝ)=2^8 by norm_num,Real.log_pow]
    norm_num
  rw [he]
  linarith

-- The complete arithmetic criterion has a concrete admitted dimension,
-- without evaluating either the 256! or the full iid sampling space.
example : distinctUniformProbability 256 256≤1/(256:ℝ)^11 :=
  endpoint_arithmetic_avoidance_bound (by decide) (by decide) arithmetic_cut_256

example : distinctUniformProbability 256 256+(255:ℝ)*dittertConstant 256 <
    (512/289:ℝ)/((256:ℝ)^3*256^2*255^2) := by
  simpa only [Nat.cast_ofNat,show (256:ℝ)-1=255 by norm_num] using
    endpoint_arithmetic_scalar_criterion (by decide : 128≤256)
    (by decide : 256≤256) arithmetic_cut_256

-- The base dimension's logarithm is controlled by an exact all-integer proof.
example : 1<Real.log (128:ℝ) := endpoint_arithmetic_log_gt_one (by decide)

-- The cut premise is indispensable; the nominal row count alone cannot
-- give the n<m² conclusion or the stated small avoidance probability.
example : ¬((22:ℝ)*128^2*Real.log 128≤(128:ℝ)*(128-1)) := by
  intro h
  have hh := endpoint_arithmetic_n_lt_square (n:=128^2) (by decide : 128≤128) (by
    norm_num at h ⊢
    exact h)
  norm_num at hh

example : ¬(distinctUniformProbability 2 2≤1/(2:ℝ)^11) := by
  norm_num [distinctUniformProbability,Nat.descFactorial]

#print axioms endpoint_arithmetic_log_gt_one
#print axioms endpoint_arithmetic_n_lt_square
#print axioms endpoint_arithmetic_avoidance_bound
#print axioms endpoint_arithmetic_scalar_criterion
end DittertRybin.Tests
