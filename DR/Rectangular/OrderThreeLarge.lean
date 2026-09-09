import DR.Rectangular.OrderThreeLargeNear
import DR.Rectangular.OrderThreeSampling
import DR.Maximizers
import Lean.Elab.Tactic.Omega

/-!
# Unique three-sample maxima on large rectangles and infinite strips

The theorem combines actual iid failure probabilities with exact near/far
bounds on the full closed matrix simplex. No support restriction is imposed.
-/

namespace DittertRybin

theorem orderThreeFailurePolynomial_strict_of_criterion {m n : ℕ}
    (hm : 3 ≤ m) (hmn : m ≤ n) (hcriterion : 0 < orderThreeLargeCriterion m n)
    {P : Board m n} (hP : IsProbability P) (hPU : P ≠ uniformBoard m n) :
    orderThreeFailurePolynomial (uniformBoard m n) < orderThreeFailurePolynomial P := by
  have hE : 0 < orderThreeSquareSum (orderThreeCentered P) := by
    have hnonneg := orderThreeSquareSum_nonneg (orderThreeCentered P)
    have hne : orderThreeSquareSum (orderThreeCentered P) ≠ 0 := by
      intro h
      apply hPU
      exact (orderThreeCentered_eq_zero_iff P).mp
        ((orderThreeSquareSum_eq_zero_iff _).mp h)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  by_cases hnear : orderThreeSquareSum (orderThreeCentered P) ≤ 2 * ((m : ℝ) * n)⁻¹
  · have h := orderThreeFailurePolynomial_near hm hmn hP hnear
    have hp := mul_pos hcriterion hE
    linarith
  · exact orderThreeFailurePolynomial_far hm (hm.trans hmn) hP (le_of_lt (lt_of_not_ge hnear))

/-- The retained scalar criterion proves both the actual maximum and exact equality case. -/
theorem uniform_maximum_order_three_of_large_criterion {m n : ℕ}
    (hm : 3 ≤ m) (hmn : m ≤ n) (hcriterion : 0 < orderThreeLargeCriterion m n) :
    UniformMaximizer m n 3 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := hm0.trans_le hmn
  have hU := uniformBoard_isProbability hm0 hn0
  have hu := separationProbability_uniform (k := 3) hm0 hn0
  intro P hP
  by_cases hPU : P = uniformBoard m n
  · subst P
    exact ⟨hu.le, iff_of_true hu rfl⟩
  · have hQ := orderThreeFailurePolynomial_strict_of_criterion hm hmn hcriterion hP hPU
    have hPpoly := one_sub_separationProbability_three hP
    have hUpoly := one_sub_separationProbability_three hU
    have hstrict : separationProbability P 3 < uniformSeparationValue m n 3 := by linarith
    exact ⟨hstrict.le, iff_of_false (ne_of_lt hstrict) hPU⟩

/-- The unique-maximizer statement is invariant under exchanging the two axes. -/
theorem UniformMaximizer.transpose {m n k : ℕ} (h : UniformMaximizer m n k) :
    UniformMaximizer n m k := by
  intro P hP
  have hv : uniformSeparationValue m n k = uniformSeparationValue n m k := by
    unfold uniformSeparationValue
    ring
  have ht := h P.transpose hP.transpose
  rw [separationProbability_transpose, hv] at ht
  have heq : P.transpose = uniformBoard m n ↔ P = uniformBoard n m := by
    constructor
    · intro hmat
      ext i j
      have hij := congrFun (congrFun hmat j) i
      change P i j = ((m : ℝ) * n)⁻¹ at hij
      change P i j = ((n : ℝ) * m)⁻¹
      simpa only [mul_comm] using hij
    · rintro rfl
      ext i j
      change ((n : ℝ) * m)⁻¹ = ((m : ℝ) * n)⁻¹
      rw [mul_comm]
  exact ⟨ht.1, ht.2.trans heq⟩

theorem uniform_maximum_order_three_of_min_ge_ten {m n : ℕ}
    (hm : 10 ≤ m) (hn : 10 ≤ n) : UniformMaximizer m n 3 := by
  by_cases hmn : m ≤ n
  · exact uniform_maximum_order_three_of_large_criterion (by omega) hmn
      (orderThreeLargeDimensions_ge_ten hm hmn).2
  · exact (uniform_maximum_order_three_of_large_criterion (by omega) (le_of_not_ge hmn)
      (orderThreeLargeDimensions_ge_ten hn (le_of_not_ge hmn)).2).transpose

theorem uniform_maximum_order_three_six {n : ℕ} (hn : 238 ≤ n) : UniformMaximizer 6 n 3 :=
  uniform_maximum_order_three_of_large_criterion (by norm_num) (by omega)
    (orderThreeLargeDimensions_six hn).2

theorem uniform_maximum_order_three_seven {n : ℕ} (hn : 25 ≤ n) : UniformMaximizer 7 n 3 :=
  uniform_maximum_order_three_of_large_criterion (by norm_num) (by omega)
    (orderThreeLargeDimensions_seven hn).2

theorem uniform_maximum_order_three_eight {n : ℕ} (hn : 15 ≤ n) : UniformMaximizer 8 n 3 :=
  uniform_maximum_order_three_of_large_criterion (by norm_num) (by omega)
    (orderThreeLargeDimensions_eight hn).2

theorem uniform_maximum_order_three_nine {n : ℕ} (hn : 12 ≤ n) : UniformMaximizer 9 n 3 :=
  uniform_maximum_order_three_of_large_criterion (by norm_num) (by omega)
    (orderThreeLargeDimensions_nine hn).2

/-- A strip theorem covers both orientations of the smaller and larger dimensions. -/
theorem uniform_maximizer_strip_transfer {r N k : ℕ}
    (hstrip : ∀ n, N ≤ n → UniformMaximizer r n k) {m n : ℕ}
    (hmin : min m n = r) (hmax : N ≤ max m n) : UniformMaximizer m n k := by
  by_cases hmn : m ≤ n
  · have hm : m = r := by simpa only [min_eq_left hmn] using hmin
    subst m
    exact hstrip n (by simpa only [max_eq_right hmn] using hmax)
  · have hnm : n ≤ m := le_of_not_ge hmn
    have hn : n = r := by simpa only [min_eq_right hnm] using hmin
    subst n
    exact (hstrip m (by simpa only [max_eq_left hnm] using hmax)).transpose

end DittertRybin
