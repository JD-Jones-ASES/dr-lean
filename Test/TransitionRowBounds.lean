import DR.Endpoint.TransitionRowBounds
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The logarithm's positive domain and the upper-cap hypothesis matter.
example : Real.log 32≤(32:ℝ)-1-(32-1)^2/64 :=
  log_le_sub_one_sub_sq_sixty_four 32 (by norm_num) (by norm_num)
example : ¬(Real.log 0≤(0:ℝ)-1-(0-1)^2/64) := by norm_num
example : ¬(Real.log 1000≤(1000:ℝ)-1-(1000-1)^2/64) := by
  have h : 0≤Real.log 1000 := Real.log_nonneg (by norm_num)
  norm_num at h ⊢
  linarith

-- A nonconstant vector supplies the actual product input.
private noncomputable def y : Fin 2 → ℝ := ![1/2,3/2]
private theorem hy : ∀ i,0≤y i := by intro i; fin_cases i <;> norm_num [y]
private theorem hys : (∑ i,y i)=(2:ℝ) := by norm_num [y,Fin.sum_univ_succ]
private theorem hyp : (1/50000:ℝ)<∏ i,y i := by norm_num [y,Fin.prod_univ_succ]
example (i : Fin 2) : 1/150000<y i ∧ y i<32 :=
  transition_product_coordinate_bounds y hy hys hyp i
example : (∑ i,(y i-1)^2)<1024 := transition_product_sq_deviation y hy hys hyp
example : (∑ i,(y i-1)^2/y i)<160000000 :=
  transition_product_reciprocal_deviation y hy hys hyp
example : (∑ i,(y i-1)^2/y i)=(2/3:ℝ) := by norm_num [y,Fin.sum_univ_succ]
example : ¬((1/50000:ℝ)<∏ i : Fin 2,(![2,0] : Fin 2 → ℝ) i) := by
  norm_num [Fin.prod_univ_succ]

-- Empty finite products are retained in the generic scalar lemma.
example : (∑ i : Fin 0,((fun _ => (0:ℝ)) i-1)^2)<1024 := by
  apply transition_product_sq_deviation
  · intro i; exact Fin.elim0 i
  · simp
  · norm_num

example : (1/40001:ℝ)≤1-distinctUniformProbability 2 2 :=
  endpoint_transition_uniform_failure_lower (by decide) (by decide) (by norm_num)

-- Removing the n<=10000m² guard makes the uniform failure conclusion false.
example : ¬((1/40001:ℝ)≤1-distinctUniformProbability 100000000 2) := by
  rw [distinctUniformProbability_eq_product (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]

-- All hypotheses in the actual matrix bridge concern the closed simplex and
-- the real contender comparison, not prior positive rows or stationarity.
example {m n : ℕ} (hm : 2≤m) (hmn : m≤n) (hn : n≤10000*m^2)
    (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) :
    endpointRowReciprocalDeviation P<160000000 :=
  (endpoint_transition_contender_row_bounds hm hmn hn hP hcont).2.2

#print axioms coordinate_exp_envelope_le_at
#print axioms exp_neg_one_lt_half
#print axioms thirty_two_exp_neg_thirty_one_lt
#print axioms exp_neg_sixteen_lt_inv50000
#print axioms log_le_sub_one_sub_sq_sixty_four
#print axioms transition_product_coordinate_bounds
#print axioms transition_product_sq_deviation
#print axioms transition_product_reciprocal_deviation
#print axioms endpoint_transition_uniform_failure_lower
#print axioms endpoint_transition_contender_row_bounds
end DittertRybin.Tests
