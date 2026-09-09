import DR.Rectangular.OrderThreeLargeFiveNormalize

/-! The retained five-row estimate on the full closed probability simplex. -/

namespace DittertRybin

/-- A row-energy direction is normalized without requiring positive row energy. -/
theorem orderThree_row_energy_parameter {n E A : ℝ} (hn : 0 < n) (hE : 0 < E)
    (hA : 0 ≤ A) (hAE : A / n ≤ E) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ A = n * E * u ^ 2 := by
  have hnE : 0 < n * E := mul_pos hn hE
  have hAE' : A ≤ n * E := by
    have h := (div_le_iff₀ hn).mp hAE
    nlinarith
  have hratio : A / (n * E) ≤ 1 := (div_le_iff₀ hnE).mpr (by simpa using hAE')
  have hratio0 : 0 ≤ A / (n * E) := div_nonneg hA hnE.le
  refine ⟨Real.sqrt (A / (n * E)), Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hratio, ?_⟩
  rw [Real.sq_sqrt hratio0]
  field_simp

/-- A positive rational margin holds throughout the near region, including zero cells. -/
theorem orderThreeFailurePolynomial_five_near {n : ℕ} (hn : 121 ≤ n)
    {P : Board 5 n} (hP : IsProbability P)
    (hnear : orderThreeSquareSum (orderThreeCentered P) ≤ 2 * ((5 : ℝ) * n)⁻¹) :
    (27197 / 2772275 : ℝ) * orderThreeSquareSum (orderThreeCentered P) ≤
      orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard 5 n) := by
  have hn0 : 0 < n := by omega
  have hnR : (121 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  let X := orderThreeCentered P
  let E := orderThreeSquareSum X
  let A := orderThreeRowSquareSum X
  have hX : totalMass X = 0 := orderThreeCentered_totalMass (by norm_num) hn0 hP
  have hE0 : 0 ≤ E := orderThreeSquareSum_nonneg X
  by_cases hEz : E = 0
  · have hXz : X = 0 := (orderThreeSquareSum_eq_zero_iff X).mp hEz
    have hU := (orderThreeCentered_eq_zero_iff P).mp hXz
    change (27197 / 2772275 : ℝ) * E ≤ _
    rw [hEz, mul_zero, hU, sub_self]
  have hE : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEz)
  have hA : 0 ≤ A := orderThreeRowSquareSum_nonneg X
  have hAE : A / n ≤ E := by
    have hT := orderThreeMarginalSquareSum_le (by norm_num : 0 < 5) hn0 X hX
    have hB := orderThreeColSquareSum_nonneg X
    change A / n + orderThreeColSquareSum X / 5 ≤ E at hT
    linarith [div_nonneg hB (by norm_num : (0 : ℝ) ≤ 5)]
  obtain ⟨u, hu0, hu1, hAu⟩ := orderThree_row_energy_parameter hnpos hE hA hAE
  have hsize : 5 * (n : ℝ) * E ≤ 2 := by
    calc
      5 * (n : ℝ) * E ≤ (5 * (n : ℝ)) * (2 * (5 * (n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hnear (by positivity)
      _ = 2 := by field_simp
  have hnormalized := orderThree_five_normalized_bound (by linarith : (3 : ℝ) ≤ n)
    hE hu0 hu1 hsize
  rw [← hAu] at hnormalized
  have hpre := orderThreeFailurePolynomial_five_prebound (by omega : 3 ≤ n) hP
  change (9 / 5 - 22 / (5 * (n : ℝ))) * E + (18 / 5) * (A / n) -
      6 * Real.sqrt ((4 / 5) * A) * E -
      9 * (Real.sqrt ((E - A / n) * A) + E) ^ 2 /
        (6 * ((5 : ℝ) * n)⁻¹ * ((n : ℝ) - 2)) ≤ _ at hpre
  have hscalar := orderThreeFiveExpression_lower hnR hu0 hu1
  have hmargin := mul_le_mul_of_nonneg_left hscalar hE.le
  change (27197 / 2772275 : ℝ) * E ≤ _
  calc
    _ = E * (27197 / 2772275) := by ring
    _ ≤ E * orderThreeFiveExpression n u := hmargin
    _ ≤ _ := hnormalized.trans hpre

end DittertRybin
