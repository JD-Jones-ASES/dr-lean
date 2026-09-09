import DR.Rectangular.OrderThreeLargeFiveNear
import DR.Rectangular.OrderThreeLarge

/-! The unique three-sample maximum on every five-row strip of length at least 121. -/

namespace DittertRybin

theorem orderThreeFailurePolynomial_five_strict {n : ℕ} (hn : 121 ≤ n)
    {P : Board 5 n} (hP : IsProbability P) (hPU : P ≠ uniformBoard 5 n) :
    orderThreeFailurePolynomial (uniformBoard 5 n) < orderThreeFailurePolynomial P := by
  have hE : 0 < orderThreeSquareSum (orderThreeCentered P) := by
    have hnonneg := orderThreeSquareSum_nonneg (orderThreeCentered P)
    have hne : orderThreeSquareSum (orderThreeCentered P) ≠ 0 := by
      intro h
      apply hPU
      exact (orderThreeCentered_eq_zero_iff P).mp
        ((orderThreeSquareSum_eq_zero_iff _).mp h)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  by_cases hnear : orderThreeSquareSum (orderThreeCentered P) ≤ 2 * ((5 : ℝ) * n)⁻¹
  · have h := orderThreeFailurePolynomial_five_near hn hP hnear
    have hp := mul_pos (by norm_num : (0 : ℝ) < 27197 / 2772275) hE
    linarith
  · exact orderThreeFailurePolynomial_far (by norm_num) (by omega) hP
      (le_of_lt (lt_of_not_ge hnear))

/-- The actual iid functional has a unique uniform maximum on the full closed simplex. -/
theorem uniform_maximum_order_three_five {n : ℕ} (hn : 121 ≤ n) :
    UniformMaximizer 5 n 3 := by
  have hn0 : 0 < n := by omega
  have hU := uniformBoard_isProbability (by norm_num : 0 < 5) hn0
  have hu := separationProbability_uniform (k := 3) (by norm_num : 0 < 5) hn0
  intro P hP
  by_cases hPU : P = uniformBoard 5 n
  · subst P
    exact ⟨hu.le, iff_of_true hu rfl⟩
  · have hQ := orderThreeFailurePolynomial_five_strict hn hP hPU
    have hPpoly := one_sub_separationProbability_three hP
    have hUpoly := one_sub_separationProbability_three hU
    have hstrict : separationProbability P 3 < uniformSeparationValue 5 n 3 := by linarith
    exact ⟨hstrict.le, iff_of_false (ne_of_lt hstrict) hPU⟩

/-- Both orientations are included without restricting the support of the matrix. -/
theorem uniform_maximum_order_three_five_strip {m n : ℕ}
    (hmin : min m n = 5) (hmax : 121 ≤ max m n) : UniformMaximizer m n 3 :=
  uniform_maximizer_strip_transfer (fun _ hn => uniform_maximum_order_three_five hn) hmin hmax

end DittertRybin
