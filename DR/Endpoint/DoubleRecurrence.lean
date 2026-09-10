import DR.Endpoint.FactorialDecay
import DR.Endpoint.UniformAvoidanceBound
import DR.Endpoint.Normalization

/-! Exact factorial recurrences for the near-square and doubled endpoint
criteria. Rational decay bounds hold at every dimension, and the polynomial
weight comparison is uniform for the two exponents used in those criteria. -/

namespace DittertRybin
open scoped BigOperators

theorem distinctUniformProbability_factorial {m n : ℕ} (hmn : m ≤ n) :
    distinctUniformProbability n m =
      (n.factorial : ℝ) / (((n-m).factorial : ℝ) * (n : ℝ)^m) := by
  have hf : ((n-m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-m)
  have hmul : ((n-m).factorial : ℝ) * (n.descFactorial m : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hmn
  have hdesc : (n.descFactorial m : ℝ) = (n.factorial : ℝ) / ((n-m).factorial : ℝ) := by
    apply (eq_div_iff hf).mpr
    simpa only [mul_comm] using hmul
  rw [distinctUniformProbability, hdesc, div_div]

theorem distinctUniformProbability_double_factorial (m : ℕ) :
    distinctUniformProbability (2*m) m =
      ((2*m).factorial : ℝ) / ((m.factorial : ℝ) * (2 : ℝ)^m * (m : ℝ)^m) := by
  rw [distinctUniformProbability_factorial (by omega : m ≤ 2*m),
    show 2*m-m = m by omega, Nat.cast_mul, Nat.cast_ofNat, mul_pow]
  ring

/-- The exact source recurrence before any scalar estimates. -/
theorem distinctUniformProbability_double_succ {m : ℕ} (hm : 1 ≤ m) :
    distinctUniformProbability (2*(m+1)) (m+1) * (((m : ℝ)+1)/(m : ℝ))^m =
      ((2*(m : ℝ)+1)/((m : ℝ)+1)) * distinctUniformProbability (2*m) m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hp : (2 : ℝ)^m ≠ 0 := by positivity
  have hs : (m : ℝ)+1 ≠ 0 := by positivity
  rw [distinctUniformProbability_double_factorial, distinctUniformProbability_double_factorial,
    show 2*(m+1) = (2*m+1)+1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    pow_succ, div_pow]
  field_simp
  ring

theorem one_add_pow_quadratic_lower {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    1 + (m : ℝ)*x + (m : ℝ)*((m : ℝ)-1)/2*x^2 ≤ (1+x)^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | @succ m hm ih =>
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+x)
    have hrem : 0 ≤ (m : ℝ)*((m : ℝ)-1)*x^3 := by positivity
    rw [pow_succ (1+x), Nat.cast_add, Nat.cast_one]
    nlinarith only [hmul, hrem]

theorem double_recurrence_binomial_lower {m : ℕ} (hm : 5 ≤ m) :
    (12/5 : ℝ) ≤ (((m : ℝ)+1)/(m : ℝ))^m := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h := one_add_pow_quadratic_lower (by omega : 1 ≤ m)
    (x := 1/(m : ℝ)) (by positivity)
  have hleft : 1+(m : ℝ)*(1/(m : ℝ))+
      (m : ℝ)*((m : ℝ)-1)/2*(1/(m : ℝ))^2 = (5/2 : ℝ)-1/(2*(m : ℝ)) := by
    field_simp
    ring
  have hbase : 1+1/(m : ℝ) = ((m : ℝ)+1)/(m : ℝ) := by field_simp
  rw [hleft, hbase] at h
  have hsmall : 1/(2*(m : ℝ)) ≤ (1/10 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(m : ℝ))).mpr
    linarith
  linarith

/-- A simple uniform rational decay extracted from the exact doubled recurrence. -/
theorem distinctUniformProbability_double_succ_le {m : ℕ} (hm : 5 ≤ m) :
    distinctUniformProbability (2*(m+1)) (m+1) ≤
      (5/6 : ℝ) * distinctUniformProbability (2*m) m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < 2*m) (by omega : m ≤ 2*m)
  have hbnext := distinctUniformProbability_pos (by omega : 0 < 2*(m+1))
    (by omega : m+1 ≤ 2*(m+1))
  have hlow := mul_le_mul_of_nonneg_left (double_recurrence_binomial_lower hm) hbnext.le
  rw [distinctUniformProbability_double_succ (by omega)] at hlow
  have hratio : (2*(m : ℝ)+1)/((m : ℝ)+1) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
    linarith
  have hhigh := mul_le_mul_of_nonneg_right hratio hb.le
  nlinarith only [hlow, hhigh]

/-- The uniform avoidance factor increases with the number of available columns. -/
theorem distinctUniformProbability_mono_columns {m n N : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) (hnN : n ≤ N) :
    distinctUniformProbability n m ≤ distinctUniformProbability N m := by
  rw [distinctUniformProbability_eq_product hn hmn,
    distinctUniformProbability_eq_product (by omega) (hmn.trans hnN)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  apply Finset.prod_le_prod
  · intro i hi
    have hiR : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by have := Finset.mem_range.mp hi; omega)
    exact sub_nonneg.mpr ((div_le_one hnR).mpr hiR)
  · intro i _
    exact sub_le_sub_left (div_le_div_of_nonneg_left (Nat.cast_nonneg i) hnR hnNR) 1

end DittertRybin
