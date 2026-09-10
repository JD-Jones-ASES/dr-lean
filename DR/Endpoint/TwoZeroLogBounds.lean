import DR.Endpoint.TwoZeroPolynomialDerivatives
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Rigorous elementary logarithmic truncation bounds for the infinite
 two-zero scalar tail. The remainders are proved by exact derivatives and
 monotonicity, including equality at zero. -/
namespace DittertRybin

private noncomputable def logResidualThree (x : ℝ) : ℝ :=
  Real.log (1-x)+x+x^2/2+x^3/(3*(1-x))

private noncomputable def logResidualFour (x : ℝ) : ℝ :=
  Real.log (1-x)+x+x^2/2+x^3/3+x^4/(4*(1-x))

private noncomputable def logResidualPlus (x : ℝ) : ℝ :=
  Real.log (1+x)-x+x^2/2-x^3/3+x^4/4

private theorem hasDerivAt_logResidualThree {x : ℝ} (hx : x < 1) :
    HasDerivAt logResidualThree (x^3/(3*(1-x)^2)) x := by
  have hd : 1-x ≠ 0 := by linarith
  have hden : 3*(1-x) ≠ 0 := mul_ne_zero (by norm_num) hd
  have hid := hasDerivAt_id x
  have hsub := (hasDerivAt_const x (1 : ℝ)).sub hid
  convert (((hsub.log hd).add hid).add ((hid.pow 2).div_const 2)).add
    ((hid.pow 3).div (hsub.const_mul 3) hden) using 1 <;> try rfl
  all_goals try dsimp [logResidualThree]
  all_goals field_simp
  all_goals ring

private theorem hasDerivAt_logResidualFour {x : ℝ} (hx : x < 1) :
    HasDerivAt logResidualFour (x^4/(4*(1-x)^2)) x := by
  have hd : 1-x ≠ 0 := by linarith
  have hden : 4*(1-x) ≠ 0 := mul_ne_zero (by norm_num) hd
  have hid := hasDerivAt_id x
  have hsub := (hasDerivAt_const x (1 : ℝ)).sub hid
  convert ((((hsub.log hd).add hid).add ((hid.pow 2).div_const 2)).add
    ((hid.pow 3).div_const 3)).add ((hid.pow 4).div (hsub.const_mul 4) hden) using 1 <;> try rfl
  all_goals try dsimp [logResidualFour]
  all_goals field_simp
  all_goals ring

private theorem hasDerivAt_logResidualPlus {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt logResidualPlus (x^4/(1+x)) x := by
  have hd : 1+x ≠ 0 := by linarith
  have hid := hasDerivAt_id x
  have hadd := (hasDerivAt_const x (1 : ℝ)).add hid
  convert ((((hadd.log hd).sub hid).add ((hid.pow 2).div_const 2)).sub
    ((hid.pow 3).div_const 3)).add ((hid.pow 4).div_const 4) using 1 <;> try rfl
  all_goals try dsimp [logResidualPlus]
  all_goals field_simp
  all_goals ring

theorem twoZero_log_one_sub_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    -x-x^2/2-x^3/(3*(1-x)) ≤ Real.log (1-x) := by
  have hmono : MonotoneOn logResidualThree (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro y hy
      exact (hasDerivAt_logResidualThree (hy.2.trans_lt hx1)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_logResidualThree ((interior_subset hy).2.trans_lt hx1)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : y ∈ Set.Icc 0 x := interior_subset hy
      have hy0 := hy'.1
      rw [(hasDerivAt_logResidualThree (hy'.2.trans_lt hx1)).deriv]
      positivity
  have h := hmono ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  norm_num [logResidualThree] at h
  linarith

theorem twoZero_log_one_sub_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    -x-x^2/2-x^3/3-x^4/(4*(1-x)) ≤ Real.log (1-x) := by
  have hmono : MonotoneOn logResidualFour (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro y hy
      exact (hasDerivAt_logResidualFour (hy.2.trans_lt hx1)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_logResidualFour ((interior_subset hy).2.trans_lt hx1)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_logResidualFour ((interior_subset hy).2.trans_lt hx1)).deriv]
      positivity
  have h := hmono ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  norm_num [logResidualFour] at h
  linarith

theorem twoZero_log_one_add_quartic {x : ℝ} (hx : 0 ≤ x) :
    x-x^2/2+x^3/3-x^4/4 ≤ Real.log (1+x) := by
  have hmono : MonotoneOn logResidualPlus (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro y hy
      exact (hasDerivAt_logResidualPlus hy.1).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_logResidualPlus (interior_subset hy).1).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : y ∈ Set.Icc 0 x := interior_subset hy
      have hy0 := hy'.1
      rw [(hasDerivAt_logResidualPlus hy'.1).deriv]
      positivity
  have h := hmono ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  norm_num [logResidualPlus] at h
  linarith

theorem twoZero_log_one_sub_cubic_cap {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) (hc : c < 1) :
    -x-x^2/2-x^3/(3*(1-c)) ≤ Real.log (1-x) := by
  have hdiv := div_le_div_of_nonneg_left (pow_nonneg hx 3)
    (show 0 < 3*(1-c) by positivity) (show 3*(1-c) ≤ 3*(1-x) by linarith)
  have h := twoZero_log_one_sub_cubic hx (hxc.trans_lt hc)
  linarith

theorem twoZero_log_one_sub_quartic_cap {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) (hc : c < 1) :
    -x-x^2/2-x^3/3-x^4/(4*(1-c)) ≤ Real.log (1-x) := by
  have hdiv := div_le_div_of_nonneg_left (pow_nonneg hx 4)
    (show 0 < 4*(1-c) by positivity) (show 4*(1-c) ≤ 4*(1-x) by linarith)
  have h := twoZero_log_one_sub_quartic hx (hxc.trans_lt hc)
  linarith

end DittertRybin
