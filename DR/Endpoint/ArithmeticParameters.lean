import DR.Endpoint.FactorialDecay
import DR.Endpoint.UniformAvoidanceBound

/-! Exact dimension estimates for the arithmetic endpoint range. These
discharge its scalar sufficient condition; the cut, transport and boundary
permanent argument is a separate obligation. -/
namespace DittertRybin

theorem endpoint_arithmetic_log_gt_one {m : ℕ} (hm : 128≤m) :
    1<Real.log (m:ℝ) := by
  have hmR : (128:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  apply Real.exp_lt_exp.mp
  rw [Real.exp_log hm0]
  linarith [Real.exp_one_lt_d9]

theorem endpoint_arithmetic_n_lt_square {m n : ℕ} (hm : 128≤m)
    (hcut : (22:ℝ)*(n:ℝ)*Real.log (m:ℝ)≤(m:ℝ)*((m:ℝ)-1)) :
    (n:ℝ)<(m:ℝ)^2 := by
  have hmR : (128:ℝ)≤m := by exact_mod_cast hm
  have hl := endpoint_arithmetic_log_gt_one hm
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hl.le)]

theorem endpoint_arithmetic_avoidance_bound {m n : ℕ} (hm : 128≤m) (hmn : m≤n)
    (hcut : (22:ℝ)*(n:ℝ)*Real.log (m:ℝ)≤(m:ℝ)*((m:ℝ)-1)) :
    distinctUniformProbability n m≤1/(m:ℝ)^11 := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hn : 0<n := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have he : (11:ℝ)*Real.log (m:ℝ)≤(m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    nlinarith only [hcut]
  have hexp : Real.exp ((11:ℝ)*Real.log (m:ℝ))=(m:ℝ)^11 := by
    rw [show (11:ℝ)=(11:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hm0]
  calc
    distinctUniformProbability n m≤Real.exp (-((m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)))) :=
      distinctUniformProbability_le_exp hn hmn
    _≤Real.exp (-((11:ℝ)*Real.log (m:ℝ))) := Real.exp_le_exp.mpr (neg_le_neg he)
    _=1/(m:ℝ)^11 := by rw [Real.exp_neg,hexp,inv_eq_one_div]

/-- The elementary arithmetic cutoff implies the strict scalar boundary
criterion with c₀=(16/17)² and no gcd improvement. -/
theorem endpoint_arithmetic_scalar_criterion {m n : ℕ} (hm : 128≤m) (hmn : m≤n)
    (hcut : (22:ℝ)*(n:ℝ)*Real.log (m:ℝ)≤(m:ℝ)*((m:ℝ)-1)) :
    distinctUniformProbability n m+((n:ℝ)-1)*dittertConstant m <
      (512/289:ℝ)/((m:ℝ)^3*(n:ℝ)^2*((n:ℝ)-1)^2) := by
  have hmR : (128:ℝ)≤m := by exact_mod_cast hm
  have hmnR : (m:ℝ)≤n := by exact_mod_cast hmn
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by linarith
  have hn1 : (0:ℝ)<(n:ℝ)-1 := by linarith
  have hns := endpoint_arithmetic_n_lt_square hm hcut
  have ha : dittertConstant m≤1/(m:ℝ)^14 := by
    rw [← distinctUniformProbability_self]
    exact distinctUniformProbability_endpoint_le_inv_fourteenth hm
  have hb := endpoint_arithmetic_avoidance_bound hm hmn hcut
  have hterm : ((n:ℝ)-1)*dittertConstant m<1/(m:ℝ)^12 := by
    calc
      _≤((n:ℝ)-1)*(1/(m:ℝ)^14) := mul_le_mul_of_nonneg_left ha hn1.le
      _=((n:ℝ)-1)/(m:ℝ)^14 := by ring
      _<(m:ℝ)^2/(m:ℝ)^14 := (div_lt_div_iff_of_pos_right (pow_pos hm0 14)).mpr (by linarith)
      _=1/(m:ℝ)^12 := by field_simp
  have hinv : 1/(m:ℝ)≤1/128 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
  have hsum : distinctUniformProbability n m+((n:ℝ)-1)*dittertConstant m <
      (512/289:ℝ)/(m:ℝ)^11 := by
    calc
      _<1/(m:ℝ)^11+1/(m:ℝ)^12 := add_lt_add_of_le_of_lt hb hterm
      _=(1+1/(m:ℝ))/(m:ℝ)^11 := by field_simp
      _≤(129/128:ℝ)/(m:ℝ)^11 :=
        div_le_div_of_nonneg_right (by linarith) (pow_pos hm0 11).le
      _<(512/289:ℝ)/(m:ℝ)^11 :=
        (div_lt_div_iff_of_pos_right (pow_pos hm0 11)).mpr (by norm_num)
  have hn2 : (n:ℝ)^2<(m:ℝ)^4 := by
    have hp := pow_lt_pow_left₀ hns hn0.le (by decide : (2:ℕ)≠0)
    simpa only [← pow_mul] using hp
  have hnm2 : ((n:ℝ)-1)^2<(m:ℝ)^4 := by
    have hp := pow_lt_pow_left₀ (show (n:ℝ)-1<(m:ℝ)^2 by linarith) hn1.le
      (by decide : (2:ℕ)≠0)
    simpa only [← pow_mul] using hp
  have hsmall : (n:ℝ)^2*((n:ℝ)-1)^2 < (m:ℝ)^8 := by
    calc
      _<(m:ℝ)^4*((n:ℝ)-1)^2 := mul_lt_mul_of_pos_right hn2 (sq_pos_of_pos hn1)
      _≤(m:ℝ)^4*(m:ℝ)^4 := mul_le_mul_of_nonneg_left hnm2.le (pow_pos hm0 4).le
      _=(m:ℝ)^8 := by ring
  have hden : (m:ℝ)^3*(n:ℝ)^2*((n:ℝ)-1)^2<(m:ℝ)^11 := by
    calc
      _=(m:ℝ)^3*((n:ℝ)^2*((n:ℝ)-1)^2) := by ring
      _<(m:ℝ)^3*(m:ℝ)^8 := mul_lt_mul_of_pos_left hsmall (pow_pos hm0 3)
      _=(m:ℝ)^11 := by ring
  have hden0 : 0<(m:ℝ)^3*(n:ℝ)^2*((n:ℝ)-1)^2 := by positivity
  exact hsum.trans (div_lt_div_of_pos_left (by norm_num) hden0 hden)

end DittertRybin
