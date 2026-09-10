import DR.Endpoint.ArithmeticParameters
import DR.Endpoint.LeadingConstants
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! Exact overlap of the arithmetic and local-lemma endpoint ranges.
The logarithm-to-square-root ratio decreases after exp(2); an elementary
rational bound at10^18 supplies an ample strict overlap margin. -/
namespace DittertRybin

theorem endpoint_large_log_sqrt {m : ℕ} (hm : 10^18≤m) :
    Real.log (m:ℝ)<Real.sqrt (m:ℝ)/2816 := by
  have hmR : (1000000000000000000:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have he := endpoint_exp_two_lt_seven_two_fifths
  have hratio := Real.log_div_sqrt_antitoneOn
    (show (1000000000000000000:ℝ)∈Set.Ici (Real.exp 2) from
      he.le.trans (by norm_num))
    (show (m:ℝ)∈Set.Ici (Real.exp 2) from
      he.le.trans ((show (37/5:ℝ)≤1000000000000000000 by norm_num).trans hmR)) hmR
  have hbase : Real.log (1000000000000000000:ℝ)≤162 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)
    have hid : (1000000000000000000:ℝ)=10^18 := by norm_num
    rw [hid,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hs : Real.sqrt (1000000000000000000:ℝ)=1000000000 := by norm_num
  change Real.log (m:ℝ)/Real.sqrt (m:ℝ)≤
    Real.log (1000000000000000000:ℝ)/Real.sqrt (1000000000000000000:ℝ) at hratio
  rw [hs] at hratio
  have hscaled := div_le_div_of_nonneg_right hbase (by norm_num : (0:ℝ)≤1000000000)
  have hsmall : Real.log (m:ℝ)/Real.sqrt (m:ℝ)<1/2816 :=
    (hratio.trans hscaled).trans_lt (by norm_num)
  have h := (div_lt_iff₀ (Real.sqrt_pos.mpr hm0)).mp hsmall
  nlinarith only [h]

theorem endpoint_arithmetic_lll_overlap {m n : ℕ} (hm : 10^18≤m)
    (hmn : m≤n) (hbelow : n^2<4096*m^3) :
    22*(n:ℝ)*Real.log (m:ℝ)≤(m:ℝ)*((m:ℝ)-1) := by
  have hmR : (2:ℝ)≤m := by exact_mod_cast (by omega : 2≤m)
  have hm0 : (0:ℝ)<m := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hbelowR : (n:ℝ)^2<4096*(m:ℝ)^3 := by exact_mod_cast hbelow
  have hs0 : 0<Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr hm0
  have hs2 := Real.sq_sqrt hm0.le
  have hrad : (64*(m:ℝ)*Real.sqrt (m:ℝ))^2=4096*(m:ℝ)^3 := by
    calc
      _=4096*(m:ℝ)^2*(Real.sqrt (m:ℝ))^2 := by ring
      _=_ := by rw [hs2]; ring
  have hN : (n:ℝ)<64*(m:ℝ)*Real.sqrt (m:ℝ) := by
    nlinarith only [hbelowR,hrad,mul_pos (show 0<64*(m:ℝ) by positivity) hs0]
  have hlog := endpoint_large_log_sqrt hm
  calc
    22*(n:ℝ)*Real.log (m:ℝ) ≤ 22*(n:ℝ)*(Real.sqrt (m:ℝ)/2816) :=
      mul_le_mul_of_nonneg_left hlog.le (by positivity)
    _=(n:ℝ)*(Real.sqrt (m:ℝ)/128) := by ring
    _≤(64*(m:ℝ)*Real.sqrt (m:ℝ))*(Real.sqrt (m:ℝ)/128) :=
      mul_le_mul_of_nonneg_right hN.le (by positivity)
    _=(m:ℝ)^2/2 := by
      calc
        _=(m:ℝ)*(Real.sqrt (m:ℝ))^2/2 := by ring
        _=_ := by rw [hs2]; ring
    _≤(m:ℝ)*((m:ℝ)-1) := by nlinarith only [mul_nonneg hm0.le (show 0≤(m:ℝ)-2 by linarith)]

end DittertRybin
