import DR.Endpoint.LeadingRatioBounds
import DR.Certificates.SpectralParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact scalar constants for the general endpoint gauge

The factorial ratio is exact. The exponential comparison uses Mathlib's
proved rational bound on exp(1), rather than a floating approximation.
The resulting constants are those in P0174 ENDPOINT_LEADING_GLOBAL.md.
-/
namespace DittertRybin
open scoped BigOperators

/-- The factorial sequence decreases after the first positive dimension. -/
theorem endpoint_gamma_antitone {a b : ℕ} (ha : 1≤a) (hab : a≤b) :
    dittertConstant b≤dittertConstant a := by
  induction b,hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih =>
    exact (Certificates.SpectralParameters.gamma_succ_le (by omega)).trans ih

theorem endpointLeading_alpha_le_five {m : ℕ} (hm : 5≤m) :
    dittertConstant m≤24/625 := by
  have h := endpoint_gamma_antitone (by decide : 1≤5) hm
  norm_num [dittertConstant,Nat.factorial] at h
  exact h

theorem endpointLeading_alpha_lt_thousandth {m : ℕ} (hm : 10≤m) :
    dittertConstant m<1/1000 := by
  have h := endpoint_gamma_antitone (by decide : 1≤10) hm
  norm_num [dittertConstant,Nat.factorial] at h
  change dittertConstant m≤567/1562500 at h
  linarith

theorem endpointLeadingDefect_le_two_ninths {m : ℕ} (hm : 5≤m) :
    endpointLeadingDefect m≤2/9 := by
  have h := endpoint_gamma_antitone (by decide : 1≤3) (by omega : 3≤m-2)
  norm_num [dittertConstant,Nat.factorial] at h
  change dittertConstant (m-2)≤2/9 at h
  have ha : 0≤dittertConstant (m-2) := by unfold dittertConstant; positivity
  have hi : 0≤1/(m:ℝ) := by positivity
  unfold endpointLeadingDefect
  nlinarith [mul_nonneg ha hi]

/-- The exact two-step factorial comparison underlying beta/alpha. -/
theorem endpointLeading_defect_ratio_identity {k : ℕ} (hk : 0<k) :
    dittertConstant k*(1-1/((k:ℝ)+2))=
      dittertConstant (k+2)*(1+2/(k:ℝ))^k := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hk2 : (k:ℝ)+2≠0 := by positivity
  have he : 1+2/(k:ℝ)=((k:ℝ)+2)/(k:ℝ) := by field_simp
  rw [he]
  simp only [dittertConstant,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,div_pow,pow_succ]
  field_simp
  ring

theorem endpoint_exp_two_lt_seven_two_fifths : Real.exp 2<37/5 := by
  have he := Real.exp_one_lt_d9
  have hp := Real.exp_pos 1
  have hid : Real.exp 2=Real.exp 1*Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid]
  nlinarith

theorem endpoint_binomial_two_le_exp {k : ℕ} (hk : 0<k) :
    (1+2/(k:ℝ))^k≤Real.exp 2 := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have h := pow_le_pow_left₀ (show 0≤1+2/(k:ℝ) by positivity)
    (by simpa only [add_comm] using Real.add_one_le_exp (2/(k:ℝ))) k
  have he : (Real.exp (2/(k:ℝ)))^k=Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [he] using h

theorem endpointLeadingDefect_lt_alpha_ratio {m : ℕ} (hm : 5≤m) :
    endpointLeadingDefect m<(37/5)*dittertConstant m := by
  let k := m-2
  have hk : 0<k := by omega
  have he : m=k+2 := by omega
  have hid := endpointLeading_defect_ratio_identity hk
  have hb := (endpoint_binomial_two_le_exp hk).trans_lt endpoint_exp_two_lt_seven_two_fifths
  have ha : 0<dittertConstant m := dittertConstant_pos (by omega)
  have hd : endpointLeadingDefect m=dittertConstant m*(1+2/(k:ℝ))^k := by
    unfold endpointLeadingDefect
    change dittertConstant k*(1-1/(m:ℝ))=_
    rw [he]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hid
  rw [hd]
  simpa only [mul_comm] using mul_lt_mul_of_pos_left hb ha

/-- Exact rationalization of the column-ratio cap, with a strict rational margin. -/
theorem endpointLeadingRatioCap_sub_one_lt {m : ℕ} (hm : 5≤m) :
    endpointLeadingRatioCap m-1<(1332/275)*dittertConstant m := by
  let b := endpointLeadingDefect m
  let t := Real.sqrt (1-b)
  have hb0 : 0≤b := (endpointLeadingDefect_bounds (by omega)).1
  have hb1 : b≤2/9 := endpointLeadingDefect_le_two_ninths hm
  have ht : 0<t := Real.sqrt_pos.mpr (by linarith)
  have ht2 : t^2=1-b := Real.sq_sqrt (by linarith)
  have htlo : (5/6:ℝ)<t := by nlinarith
  have hthi : t≤1 := by nlinarith
  have hden : (55/36:ℝ)≤t*(1+t) := by nlinarith
  have hC0 : 0≤endpointLeadingRatioCap m-1 := by
    change 0≤1/t-1
    have h := (one_le_div ht).mpr hthi
    linarith
  have hid : (endpointLeadingRatioCap m-1)*(t*(1+t))=b := by
    change (1/t-1)*(t*(1+t))=b
    field_simp
    nlinarith only [ht2]
  have hmul := mul_le_mul_of_nonneg_left hden hC0
  rw [hid] at hmul
  have hratio := endpointLeadingDefect_lt_alpha_ratio hm
  change b<_ at hratio
  nlinarith only [hmul,hratio]

end DittertRybin
