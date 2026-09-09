import DR.Semimatching
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact factorial decay used in the large rectangular endpoint concentration.
Bernoulli gives a_(m+1) ≤ a_m/2. An integer base and a rational ratio bound
then give a_m ≤ m⁻¹⁴ for every m≥128, without asymptotic estimates. -/

namespace DittertRybin

theorem distinctUniformProbability_endpoint_succ_le_half {m : ℕ} (hm : 1 ≤ m) :
    distinctUniformProbability (m+1) (m+1) ≤ distinctUniformProbability m m / 2 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  have hp : 0 < (m:ℝ)^m := pow_pos hmR _
  have hb := one_add_mul_le_pow (a := 1/(m:ℝ)) (by have h := one_div_pos.mpr hmR; linarith : -2 ≤ 1/(m:ℝ)) m
  have hratio : 2 ≤ (((m:ℝ)+1)/(m:ℝ))^m := by
    have he : 1+(m:ℝ)*(1/(m:ℝ)) = 2 := by field_simp; norm_num
    rw [he] at hb
    convert hb using 1
    congr 1
    field_simp
  rw [div_pow] at hratio
  have hpow : 2*(m:ℝ)^m ≤ ((m:ℝ)+1)^m := (le_div_iff₀ hp).mp hratio
  have hfactor : (0:ℝ) ≤ m.factorial := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_left hfactor (by positivity : 0 < 2*(m:ℝ)^m) hpow
  have hnext : distinctUniformProbability (m+1) (m+1) =
      (m.factorial:ℝ)/((m:ℝ)+1)^m := by
    rw [distinctUniformProbability,Nat.descFactorial_self,Nat.factorial_succ,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  rw [hnext,distinctUniformProbability,Nat.descFactorial_self]
  simpa only [div_div, mul_comm] using hdiv

/-- A geometric bound valid from m=1, including equality at the first step. -/
theorem distinctUniformProbability_endpoint_le_half_pow {m : ℕ} (hm : 1 ≤ m) :
    distinctUniformProbability m m ≤ (1/2:ℝ)^(m-1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [distinctUniformProbability]
  | @succ n hn ih =>
    have hh := distinctUniformProbability_endpoint_succ_le_half hn
    have hi := div_le_div_of_nonneg_right ih (by norm_num : (0:ℝ) ≤ 2)
    calc
      distinctUniformProbability (n+1) (n+1) ≤ (1/2:ℝ)^(n-1)/2 := hh.trans hi
      _ = (1/2:ℝ)^(n+1-1) := by
        have he : n+1-1 = (n-1)+1 := by omega
        rw [he,pow_succ]
        ring

/-- The exact rational decay comparison, proved for every integer m≥128. -/
theorem half_pow_mul_fourteenth_le_one {m : ℕ} (hm : 128 ≤ m) :
    (1/2:ℝ)^(m-1)*(m:ℝ)^14 ≤ 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | @succ n hn ih =>
    have hnR : (128:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ n := by positivity
    have hlin : (n:ℝ)+1 ≤ (129/128:ℝ)*n := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (n:ℝ)+1) hlin 14
    rw [mul_pow] at hpow
    have hratio : (129/128:ℝ)^14 ≤ 2 := by norm_num
    have hpow' : ((n:ℝ)+1)^14 ≤ 2*(n:ℝ)^14 :=
      hpow.trans (mul_le_mul_of_nonneg_right hratio (pow_nonneg hn0 _))
    have hscale := mul_le_mul_of_nonneg_left hpow' (by positivity : 0 ≤ (1/2:ℝ)^(n-1)/2)
    have he : n+1-1 = (n-1)+1 := by omega
    rw [Nat.cast_add,Nat.cast_one,he,pow_succ]
    nlinarith only [ih,hscale]

/-- The named endpoint probability itself satisfies the polynomial bound. -/
theorem distinctUniformProbability_endpoint_le_inv_fourteenth {m : ℕ} (hm : 128 ≤ m) :
    distinctUniformProbability m m ≤ 1/(m:ℝ)^14 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := mul_le_mul_of_nonneg_right (distinctUniformProbability_endpoint_le_half_pow (by omega : 1 ≤ m))
    (pow_nonneg (le_of_lt hm0) 14)
  exact (le_div_iff₀ (pow_pos hm0 14)).mpr (h.trans (half_pow_mul_fourteenth_le_one hm))

end DittertRybin
