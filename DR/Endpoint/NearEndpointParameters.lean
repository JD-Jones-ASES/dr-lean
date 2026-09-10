import DR.Endpoint.NearEndpointPadding
import DR.Endpoint.FactorialDecay

/-! All-dimension scalar estimates for the near-endpoint route. The exact
base n=26 is extended by factorial decay and a proved degree-seven weight
comparison; no finite scan or two-zero permanent premise is used. -/
namespace DittertRybin

noncomputable def nearEndpointScaleWeight (n : ℕ) : ℝ :=
  (5/3 : ℝ)*((n : ℝ)-1)^4*(n : ℝ)^3*dittertConstant n

/-- The rational polynomial weight grows by less than two at every step. -/
theorem nearEndpoint_polynomial_weight_step {x : ℝ} (hx : 26 ≤ x) :
    x^4*(x+1)^3 ≤ 2*(x-1)^4*x^3 := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 ≤ x-1 := by linarith
  have h1 : x ≤ (26/25 : ℝ)*(x-1) := by linarith
  have h2 : x+1 ≤ (27/26 : ℝ)*x := by linarith
  have hp1 := pow_le_pow_left₀ hx0 h1 4
  have hp2 := pow_le_pow_left₀ (by linarith : 0 ≤ x+1) h2 3
  have hmul := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  simp only [mul_pow] at hmul
  have hconstant : (26/25 : ℝ)^4*(27/26)^3 ≤ 2 := by norm_num
  calc
    x^4*(x+1)^3 ≤ ((26/25 : ℝ)^4*(27/26)^3)*((x-1)^4*x^3) := by nlinarith only [hmul]
    _ ≤ 2*((x-1)^4*x^3) := mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by ring

/-- The normalized scalar quantity decreases throughout the infinite tail. -/
theorem nearEndpointScaleWeight_step {n : ℕ} (hn : 26 ≤ n) :
    nearEndpointScaleWeight (n+1) ≤ nearEndpointScaleWeight n := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hgamma := distinctUniformProbability_endpoint_succ_le_half (by omega : 1 ≤ n)
  simp only [distinctUniformProbability_self] at hgamma
  have hg0 : 0 ≤ dittertConstant n := (endpoint_a_pos (by omega)).le
  have hpoly := nearEndpoint_polynomial_weight_step hnR
  have h1 := mul_le_mul_of_nonneg_left hgamma
    (show 0 ≤ (5/3 : ℝ)*(n : ℝ)^4*((n : ℝ)+1)^3 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ (5/6 : ℝ)*dittertConstant n by positivity)
  unfold nearEndpointScaleWeight
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  nlinarith only [h1,h2]

set_option maxRecDepth 4096 in
theorem nearEndpointScaleWeight_base : nearEndpointScaleWeight 26 < (3/4 : ℝ) := by
  norm_num [nearEndpointScaleWeight,dittertConstant,Nat.factorial]

theorem nearEndpointScaleWeight_lt_one {n : ℕ} (hn : 26 ≤ n) :
    nearEndpointScaleWeight n < 1 := by
  have hle : nearEndpointScaleWeight n ≤ nearEndpointScaleWeight 26 := by
    induction n,hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (nearEndpointScaleWeight_step hn).trans ih
  exact (hle.trans_lt nearEndpointScaleWeight_base).trans (by norm_num)

/-- The precise elementary factorial estimate required by the padding route. -/
theorem nearEndpoint_uniform_small {n : ℕ} (hn : 26 ≤ n) :
    distinctUniformProbability n (n-1) <
      3/(5*((n : ℝ)-1)^4*(n : ℝ)^2) := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have h := nearEndpointScaleWeight_lt_one hn
  unfold nearEndpointScaleWeight at h
  rw [distinctUniformProbability_pred (by omega)]
  apply (lt_div_iff₀ (by positivity : 0 < 5*((n : ℝ)-1)^4*(n : ℝ)^2)).mpr
  nlinarith only [h]

/-- The chosen two-zero improvement has a uniform rational scaling margin. -/
theorem nearEndpoint_gap_scalar {m : ℝ} (hm : 2 ≤ m) :
    1/(5*m^2) < ((1+1/(4*m^2))-1)/(1+1/(4*m^2))^2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 4 ≤ m^2 := by nlinarith
  have hden : 0 < (1+1/(4*m^2))^2 := by positivity
  apply (lt_div_iff₀ hden).mpr
  have hd : 0 < 80*m^6 := by positivity
  apply (mul_lt_mul_iff_right₀ hd).mp
  field_simp
  nlinarith [sq_nonneg (m^2-4)]

/-- The three scalar hypotheses of balanced domination and the final scaling
contradiction all hold for every n≥26. -/
theorem nearEndpoint_parameter_bounds {n : ℕ} (hn : 26 ≤ n) :
    distinctUniformProbability n (n-1) < 1/4 ∧
      (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1 ∧
      ((n-1 : ℕ) : ℝ)^2*distinctUniformProbability n (n-1)*((4/3 : ℝ)*(n : ℝ)^2)/4 <
        ((1+1/(4*((n : ℝ)-1)^2))-1)/(1+1/(4*((n : ℝ)-1)^2))^2 := by
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have ha := nearEndpoint_uniform_small hn
  have hpos := distinctUniformProbability_pos (by omega : 0 < n) (Nat.sub_le n 1)
  have hmul := (lt_div_iff₀ (by positivity : 0 < 5*((n : ℝ)-1)^4*(n : ℝ)^2)).mp ha
  have hm4 : 16 ≤ ((n : ℝ)-1)^4 := by
    have hsq : 4 ≤ ((n : ℝ)-1)^2 := by nlinarith
    nlinarith
  have hn2 : 4 ≤ (n : ℝ)^2 := by nlinarith
  have hL : (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1 := by
    have hw := mul_le_mul_of_nonneg_right hm4
      (show 0 ≤ 5*(n : ℝ)^2*distinctUniformProbability n (n-1) by positivity)
    nlinarith only [hmul,hw]
  refine ⟨?_,hL,?_⟩
  · have hw := mul_le_mul_of_nonneg_right hn2 hpos.le
    nlinarith only [hL,hw]
  · apply lt_trans _ (nearEndpoint_gap_scalar (by linarith : 2 ≤ (n : ℝ)-1))
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    apply (lt_div_iff₀ (by positivity : 0 < 5*((n : ℝ)-1)^2)).mpr
    nlinarith only [hmul]

end DittertRybin
