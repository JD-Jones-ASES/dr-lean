import DR.Endpoint.LongColumnVariance
import DR.Endpoint.Caps
import DR.Endpoint.FactorialDecay

/-! Exact factorial bounds and the initial column cap for every contender
with at least16 rows. No long-column P2 theorem is used as an input. -/
namespace DittertRybin

theorem longColumn_alpha_weighted_le {m : ℕ} (hm : 16≤m) :
    128*(m:ℝ)^3*dittertConstant m≤1 := by
  induction m,hm using Nat.le_induction with
  | base => norm_num [dittertConstant,Nat.factorial]
  | succ m hm ih =>
    have hmR : (16:ℝ)≤m := by exact_mod_cast hm
    have hm0 : (0:ℝ)≤m := by positivity
    have hlin : (m:ℝ)+1≤(17/16:ℝ)*m := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(m:ℝ)+1) hlin 3
    rw [mul_pow] at hpow
    have hratio : (17/16:ℝ)^3≤2 := by norm_num
    have hp : ((m:ℝ)+1)^3≤2*(m:ℝ)^3 :=
      hpow.trans (mul_le_mul_of_nonneg_right hratio (pow_nonneg hm0 3))
    have hhalf := distinctUniformProbability_endpoint_succ_le_half (by omega : 1≤m)
    rw [distinctUniformProbability_self,distinctUniformProbability_self] at hhalf
    have hmul := mul_le_mul hp hhalf
      (dittertConstant_pos (by omega : 0<m+1)).le
      (by positivity : (0:ℝ)≤2*(m:ℝ)^3)
    rw [Nat.cast_succ]
    nlinarith only [ih,hmul]

theorem longColumn_alpha_lt {m : ℕ} (hm : 16≤m) :
    dittertConstant m<1/625000 := by
  have h := endpoint_gamma_antitone (by decide : 1≤16) hm
  norm_num [dittertConstant,Nat.factorial] at h
  change dittertConstant m≤638512875/562949953421312 at h
  linarith

theorem longColumn_column_radius_lt {m : ℕ} (hm : 16≤m) :
    Real.sqrt (2*dittertConstant m/((m:ℝ)*(1-dittertConstant m)))<1/(7*(m:ℝ)^2) := by
  have hmR : (16:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have ha0 := (dittertConstant_pos (by omega : 0<m)).le
  have ha := longColumn_alpha_lt hm
  have hweight := longColumn_alpha_weighted_le hm
  have hwm := mul_le_mul_of_nonneg_right hweight hm0.le
  have hma := mul_lt_mul_of_pos_left ha hm0
  have hd : 0<(m:ℝ)*(1-dittertConstant m) := mul_pos hm0 (by linarith)
  apply (Real.sqrt_lt' (by positivity : 0<1/(7*(m:ℝ)^2))).mpr
  have he : (1/(7*(m:ℝ)^2))^2=1/(49*(m:ℝ)^4) := by field_simp; ring
  rw [he]
  apply (div_lt_div_iff₀ hd (by positivity : 0<49*(m:ℝ)^4)).mpr
  nlinarith only [hwm,hma,hm0]

theorem longColumn_contender_initial_cap {m n : ℕ} (hm : 16≤m)
    (hn : 6*m^2≤n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    colSum P j<1/(3*(m:ℝ)^2) := by
  have hmR : (16:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hmn : m≤n := by
    have h : m≤m^2 := Nat.le_self_pow (by decide) m
    omega
  have hnR : (6:ℝ)*(m:ℝ)^2≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by nlinarith
  have hcap := (endpoint_contender_column_cap (by omega : 2≤m) hmn hP hcont j).trans_lt
    (add_lt_add_right (longColumn_column_radius_lt hm) (1/(n:ℝ)))
  have hinv : 1/(n:ℝ)≤1/(6*(m:ℝ)^2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hnR
  have hsum : 1/(6*(m:ℝ)^2)+1/(7*(m:ℝ)^2)<1/(3*(m:ℝ)^2) := by
    field_simp
    nlinarith only [sq_pos_of_pos hm0]
  linarith

noncomputable def endpointColumnLossFactor (m : ℕ) : ℝ :=
  ((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2

theorem endpointColumnLossFactor_eq {m : ℕ} (hm : 2≤m) :
    endpointColumnLossFactor m=((m:ℝ)-2)*((m:ℝ)+1)/2 := by
  simp only [endpointColumnLossFactor,Nat.cast_sub hm,Nat.cast_ofNat]
  ring

theorem endpointColumnLossFactor_bounds {m : ℕ} (hm : 3≤m) :
    0<endpointColumnLossFactor m ∧ endpointColumnLossFactor m<(m:ℝ)^2/2 := by
  rw [endpointColumnLossFactor_eq (by omega)]
  have hmR : (3:ℝ)≤m := by exact_mod_cast hm
  constructor
  · exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  · nlinarith

theorem longColumn_scalar_parameters {m : ℕ} (hm : 16≤m) :
    dittertConstant m*endpointColumnLossFactor m<1 ∧
      endpointColumnLossFactor m*(endpointLeadingRho m)^2<1 := by
  let a := dittertConstant m
  let b := endpointColumnLossFactor m
  have ha : 0<a := dittertConstant_pos (by omega)
  have haU := longColumn_alpha_lt hm
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hw := longColumn_alpha_weighted_le hm
  have hmR : (16:ℝ)≤m := by exact_mod_cast hm
  have hstep := mul_nonneg (show 0≤128*(m:ℝ)-1 by linarith)
    (mul_nonneg ha.le (sq_nonneg (m:ℝ)))
  have ha2 : a*(m:ℝ)^2≤1 := by nlinarith only [hw,hstep]
  have hab := mul_lt_mul_of_pos_left hb.2 ha
  have hab1 : a*b<1 := by change a*b<a*((m:ℝ)^2/2) at hab; nlinarith only [hab,ha2]
  constructor
  · exact hab1
  · have hr := endpointLeadingRho_bounds (by omega : 5≤m)
    have hr2 := pow_le_pow_left₀ hr.1 hr.2.2 2
    have hbr := mul_le_mul_of_nonneg_left hr2 hb.1.le
    have hab2 := mul_lt_mul_of_pos_left hab1 (show 0<25*a by positivity)
    change b*(endpointLeadingRho m)^2<1
    change a<1/625000 at haU
    nlinarith only [hbr,hab2,haU]

theorem longColumn_contender_initial_loss {m n : ℕ} (hm : 16≤m)
    (hn : 6*m^2≤n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    endpointColumnLossFactor m*colSum P j<1/6 := by
  have hcap := longColumn_contender_initial_cap hm hn hP hcont j
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hmul := mul_lt_mul_of_pos_left hcap hb.1
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hmax := mul_lt_mul_of_pos_right hb.2 (by positivity : 0<1/(3*(m:ℝ)^2))
  have he : ((m:ℝ)^2/2)*(1/(3*(m:ℝ)^2))=1/6 := by field_simp; norm_num
  rw [he] at hmax
  exact hmul.trans hmax

end DittertRybin
