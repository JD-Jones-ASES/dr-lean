import DR.Endpoint.TwoZeroPolynomialDerivatives

/-! Certified cubic brackets give a lower bound for every feasible pair of
exceptional parameters, including either zero diagonal. Matrix-face reduction
is deliberately outside the hypotheses and conclusions of this scalar module. -/
namespace DittertRybin

private theorem twoZeroUnivariate_derivative_prefactor_nonneg {m : ℕ} (hm : 4 ≤ m)
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 2*(m.factorial : ℝ)*(twoZeroX m u)^(m-3)/(m : ℝ)^6*
      ((m : ℝ)-2+((m : ℝ)+2)*u) := by
  have hx := twoZeroX_pos hm hu
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 0 ≤ (m : ℝ)-2 := by linarith
  have htail : 0 ≤ (m : ℝ)-2+((m : ℝ)+2)*u := by positivity
  positivity

theorem twoZeroUnivariate_antitoneOn_left {m : ℕ} (hm : 4 ≤ m)
    {ell : ℝ} (hf : twoZeroCubic m ell ≤ 0) :
    AntitoneOn (twoZeroUnivariate m) (Set.Icc 0 ell) := by
  have hd : Differentiable ℝ (twoZeroUnivariate m) := fun u =>
    (hasDerivAt_twoZeroUnivariate hm u).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hd.continuous.continuousOn hd.differentiableOn
  intro u hu
  have hu' : u ∈ Set.Icc 0 ell := interior_subset hu
  rw [(hasDerivAt_twoZeroUnivariate hm u).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos (twoZeroUnivariate_derivative_prefactor_nonneg hm hu'.1)
  exact ((twoZeroCubic_strictMono hm).monotone hu'.2).trans hf

theorem twoZeroUnivariate_monotoneOn_right {m : ℕ} (hm : 4 ≤ m)
    {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ twoZeroCubic m r) :
    MonotoneOn (twoZeroUnivariate m) (Set.Icc r 1) := by
  have hd : Differentiable ℝ (twoZeroUnivariate m) := fun u =>
    (hasDerivAt_twoZeroUnivariate hm u).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hd.continuous.continuousOn hd.differentiableOn
  intro u hu
  have hu' : u ∈ Set.Icc r 1 := interior_subset hu
  rw [(hasDerivAt_twoZeroUnivariate hm u).deriv]
  apply mul_nonneg (twoZeroUnivariate_derivative_prefactor_nonneg hm (hr.trans hu'.1))
  exact hf.trans ((twoZeroCubic_strictMono hm).monotone hu'.1)

private theorem twoZeroUnivariate_bracket_middle {m : ℕ} (hm : 4 ≤ m)
    {ell r u : ℝ} (hl : 0 ≤ ell) (hlu : ell ≤ u) (hur : u ≤ r)
    (hr : r ≤ 1/(m : ℝ)) :
    (m.factorial : ℝ)*(twoZeroX m ell)^(m-2)*twoZeroH m r ≤ twoZeroUnivariate m u := by
  have hu : 0 ≤ u := hl.trans hlu
  have hr0 : 0 ≤ r := hu.trans hur
  have hp := pow_le_pow_left₀ (twoZeroX_pos hm hl).le (twoZeroX_monotone m hlu) (m-2)
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (m.factorial : ℝ) by positivity)
  have hh := twoZeroH_antitoneOn hm (show u ∈ Set.Icc 0 (1/(m : ℝ)) from ⟨hu,hur.trans hr⟩)
    (show r ∈ Set.Icc 0 (1/(m : ℝ)) from ⟨hr0,hr⟩) hur
  have hx := twoZeroX_pos hm hu
  exact mul_le_mul hmul hh (twoZeroH_nonneg hm hr0) (by positivity)

/-- A sign-certified cubic bracket bounds the univariate permanent everywhere
on its feasible interval; no exact root or interior minimizer is assumed. -/
theorem twoZeroUnivariate_lower_of_bracket {m : ℕ} (hm : 4 ≤ m)
    {ell r u : ℝ} (hl : 0 ≤ ell) (hlr : ell ≤ r) (hr : r ≤ 1/(m : ℝ))
    (hfl : twoZeroCubic m ell ≤ 0) (hfr : 0 ≤ twoZeroCubic m r)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (m.factorial : ℝ)*(twoZeroX m ell)^(m-2)*twoZeroH m r ≤ twoZeroUnivariate m u := by
  have hr0 : 0 ≤ r := hl.trans hlr
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hr1 : r ≤ 1 := hr.trans ((div_le_one hM0).mpr (by linarith))
  rcases le_total u ell with hul | hlu
  · exact (twoZeroUnivariate_bracket_middle hm hl le_rfl hlr hr).trans
      (twoZeroUnivariate_antitoneOn_left hm hfl ⟨hu,hul⟩ ⟨hl,le_rfl⟩ hul)
  · rcases le_total u r with hur | hru
    · exact twoZeroUnivariate_bracket_middle hm hl hlu hur hr
    · exact (twoZeroUnivariate_bracket_middle hm hl hlr le_rfl hr).trans
        (twoZeroUnivariate_monotoneOn_right hm hr0 hfr ⟨le_rfl,hr1⟩ ⟨hru,hu1⟩ hru)

/-- The full two-parameter lower bound consumed by actual two-zero face
reduction. Both parameters retain their closed feasibility bounds. -/
theorem twoZeroReducedPermanent_lower_of_bracket {m : ℕ} (hm : 4 ≤ m)
    {a b ell r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ))
    (hl : 0 ≤ ell) (hlr : ell ≤ r) (hr : r ≤ 1/(m : ℝ))
    (hfl : twoZeroCubic m ell ≤ 0) (hfr : 0 ≤ twoZeroCubic m r) :
    (m.factorial : ℝ)*(twoZeroX m ell)^(m-2)*twoZeroH m r ≤
      twoZeroReducedPermanent m a b := by
  have hM0 : (0 : ℝ) < m := by positivity
  have ham : (m : ℝ)*a ≤ 1 := by
    have h := (le_div_iff₀ hM0).mp haM
    nlinarith only [h]
  have hbm : (m : ℝ)*b ≤ 1 := by
    have h := (le_div_iff₀ hM0).mp hbM
    nlinarith only [h]
  let u := 1-(m : ℝ)*((a+b)/2)
  have hu : 0 ≤ u := by dsimp [u]; nlinarith only [ham,hbm]
  have hu1 : u ≤ 1 := by
    have hp : 0 ≤ (m : ℝ)*((a+b)/2) := by positivity
    dsimp [u]
    linarith
  have heq : (1-u)/(m : ℝ) = (a+b)/2 := by
    dsimp [u]
    field_simp
    ring
  have hd := twoZeroReducedPermanent_diagonal (by omega : 0 < m) u
  rw [heq] at hd
  exact (twoZeroUnivariate_lower_of_bracket hm hl hlr hr hfl hfr hu hu1).trans
    (hd ▸ twoZeroReducedPermanent_equalize hm ha hb haM hbM)

end DittertRybin
