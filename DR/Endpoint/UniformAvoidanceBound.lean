import DR.Endpoint.RowProductConcentration
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The actual uniform independent-row avoidance probability, bounded through
its finite product. The exponent retains the unordered-pair factor one half. -/
namespace DittertRybin
open scoped BigOperators

theorem distinctUniformProbability_eq_product {m n : ℕ} (hn : 0<n) (hmn : m≤n) :
    distinctUniformProbability n m = ∏ i ∈ Finset.range m, (1-(i:ℝ)/(n:ℝ)) := by
  have hn0 : (n:ℝ)≠0 := by positivity
  unfold distinctUniformProbability
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have he : (∏ i ∈ Finset.range m, ((n-i:ℕ):ℝ)) =
      ∏ i ∈ Finset.range m, ((n:ℝ)-(i:ℝ)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]
  rw [he]
  have hd : (n:ℝ)^m = ∏ _i ∈ Finset.range m, (n:ℝ) := by simp
  rw [hd, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  field_simp

theorem sum_range_real_eq_half (m : ℕ) :
    (∑ i ∈ Finset.range m, (i:ℝ)) = (m:ℝ)*((m:ℝ)-1)/2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [Finset.sum_range_succ,ih,Nat.cast_succ]; ring

theorem distinctUniformProbability_le_exp {m n : ℕ} (hn : 0<n) (hmn : m≤n) :
    distinctUniformProbability n m ≤ Real.exp (-((m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)))) := by
  rw [distinctUniformProbability_eq_product hn hmn]
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hprod : (∏ i ∈ Finset.range m, (1-(i:ℝ)/(n:ℝ))) ≤
      ∏ i ∈ Finset.range m, Real.exp (-(i:ℝ)/(n:ℝ)) := by
    apply Finset.prod_le_prod
    · intro i hi
      have hiN : i≤n := by have := Finset.mem_range.mp hi; omega
      have hiR : (i:ℝ)≤n := by exact_mod_cast hiN
      exact sub_nonneg.mpr ((div_le_one hnR).mpr hiR)
    · intro i _
      simpa only [neg_div, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(i:ℝ)/(n:ℝ))
  apply hprod.trans_eq
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib, sum_range_real_eq_half]
  ring

theorem exp_neg_ten_lt_inv16384 : Real.exp (-10) < (1:ℝ)/16384 := by
  have he : (8/3:ℝ)<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 : Real.exp (-1)<(3/8:ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    linarith
  have hp := pow_lt_pow_left₀ h1 (Real.exp_pos (-1)).le (by decide : (10:ℕ)≠0)
  have hid : Real.exp (-10) = (Real.exp (-1))^10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hid]
  exact hp.trans (by norm_num)

/-- The accepted upper edge of the LLL strip forces the genuine uniform
column-avoidance probability below the row-concentration threshold. -/
theorem distinctUniformProbability_small_of_twenty_mul_le {m n : ℕ}
    (hm : 2≤m) (hmn : m≤n) (hupper : 20*n≤m*(m-1)) :
    distinctUniformProbability n m < (1:ℝ)/16384 := by
  have hn : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hu : (20:ℝ)*(n:ℝ)≤(m:ℝ)*((m:ℝ)-1) := by
    have hcast : ((20*n:ℕ):ℝ)≤((m*(m-1):ℕ):ℝ) := by exact_mod_cast hupper
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub (by omega : 1≤m)] using hcast
  have hq : (10:ℝ)≤(m:ℝ)*((m:ℝ)-1)/(2*(n:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(n:ℝ))).mpr
    nlinarith
  exact ((distinctUniformProbability_le_exp hn hmn).trans
    (Real.exp_le_exp.mpr (by linarith))).trans_lt exp_neg_ten_lt_inv16384

end DittertRybin
