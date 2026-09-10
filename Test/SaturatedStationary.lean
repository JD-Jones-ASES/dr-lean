import DR.Endpoint.SaturatedStationary
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The shifted polynomial covers the exact threshold and every larger real dimension.
example : (1184/121 : ℝ)^2*(96-1) <
    (1-(1/2000 : ℝ))*(96^2-(1184/121 : ℝ)^2) :=
  saturated_variance_scalar_gap (by norm_num) (by norm_num)

-- Lowering this sufficient threshold to95 fails; this is not a counterexample to P2.
example : ¬(1184/121 : ℝ)^2*(95-1) <
    (999/1000 : ℝ)*(95^2-(1184/121 : ℝ)^2) := by norm_num

-- The exact spread constant retains the full positive pair coefficient.
example : (1332/275 : ℝ)/(495/1000) = 1184/121 := by norm_num

example : Real.sqrt (1-(1/2000 : ℝ))+(1/2000 : ℝ)/1000 < 1 :=
  (saturated_sqrt_cap (by norm_num : (0 : ℝ)<1/2000) (by norm_num)).2

-- Nonzero variance is allowed and the nonlinear penalty retains its denominator.
example : 2*((1/2000 : ℝ)*100^2/(1000*(1+3)^2))*(1/100)*(1/100) ≤
    (4/1000 : ℝ)*(1/2000) :=
  saturated_pair_penalty_cap (by norm_num) (by norm_num) (by norm_num) rfl
    (by norm_num) (by norm_num)

-- The pointwise square estimate does not assume positive or normalized rows.
example (i : Fin 2) : (![2,-1] : Fin 2 → ℝ) i ^ 2 ≤
    2*(1+(2 : ℝ)^2*marginalVariance (![2,-1] : Fin 2 → ℝ))/(2 : ℝ)^2 :=
  saturated_row_square_cap (by decide) _ i

private noncomputable def twoRows : Fin 2 → ℝ := ![1/3,2/3]
private theorem twoRows_pos (i : Fin 2) : 0 < twoRows i := by
  fin_cases i <;> norm_num [twoRows]
private theorem twoRows_sum : (∑ i, twoRows i)=1 := by
  norm_num [twoRows, Fin.sum_univ_succ]
private theorem twoRows_spread (i j : Fin 2) :
    |1/twoRows i-1/twoRows j| < (7/4 : ℝ) := by
  fin_cases i <;> fin_cases j <;> norm_num [twoRows]

example (i : Fin 2) : (2 : ℝ)-7/4 < 1/twoRows i ∧ 1/twoRows i < (2 : ℝ)+7/4 :=
  saturated_reciprocal_interval twoRows twoRows_pos twoRows_sum twoRows_spread i

example : marginalVariance twoRows < (7/4 : ℝ)^2/((2 : ℝ)*((2 : ℝ)^2-(7/4 : ℝ)^2)) :=
  saturated_interval_variance_bound (by decide) twoRows twoRows_sum (by norm_num)
    (by norm_num) (saturated_row_interval twoRows twoRows_pos twoRows_sum
      (by norm_num) (by norm_num) twoRows_spread)

-- The interval identity detects omission of the mass-one hypothesis.
example : marginalVariance (fun _ : Fin 2 => (2 : ℝ)) ≠
    (∑ _i : Fin 2, (2 : ℝ)^2)-1/(2 : ℝ) := by
  norm_num [marginalVariance]

-- Non-vacuous rational moment data. Both the moment inequality and the
-- square-root cap are verified exactly over the reals.
example : (499/1000 : ℝ)*(1/2000) < (1/4000 : ℝ)+1/10000000 := by
  apply saturated_moment_lower (G := (3999/4000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) _ (by norm_num)
  have hs : (3999/4000 : ℝ)-(1/2000 : ℝ)/1000 ≤ Real.sqrt (1-(1/2000 : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  linarith

-- The final actual leading kernel is strictly positive at uniform96 rows.
set_option maxRecDepth 4096 in
example : (endpointLeadingKernel (fun _ : Fin 96 => (1/96 : ℝ))).PosDef := by
  apply endpointLeadingKernel_posDef
  · norm_num
  · norm_num
  · norm_num [endpointLeadingScale, Nat.factorial]

-- Positivity of the pair coefficient is essential to control a reciprocal spread.
example : |1/(1/100 : ℝ)-1/(1 : ℝ)| > (1184/121 : ℝ) ∧
    (0 : ℝ) = (0-2*0*(1/100)*1)*(1/(1/100)-1/1) := by norm_num

#print axioms saturated_sqrt_cap
#print axioms saturated_moment_lower
#print axioms saturated_pair_penalty_cap
#print axioms saturated_stationarity_pair
#print axioms saturated_reciprocal_spread
#print axioms saturated_variance_scalar_gap
#print axioms saturated_row_square_cap
#print axioms saturated_reciprocal_interval
#print axioms saturated_row_interval
#print axioms saturated_interval_variance_bound
#print axioms saturated_rows_psd_criterion
#print axioms saturated_stationary_reciprocal_bounds
#print axioms saturated_stationary_kernel

end DittertRybin.Tests
