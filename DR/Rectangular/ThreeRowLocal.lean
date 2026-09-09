import DR.Rectangular.OrderThreeLargeExpansion
import DR.Rectangular.OrderThreeSampling

/-!
# Strict local uniqueness of the uniform three-sample maximum

The centered cubic has a positive definite quadratic part whenever both
dimensions are at least three. Explicit finite norm estimates bound all
cubic terms by a constant times the three-halves power of the cell energy.
The resulting neighborhood is valid on the full closed probability simplex.
-/

namespace DittertRybin
open scoped BigOperators

/-- The least coefficient in the centered quadratic part. -/
noncomputable def orderThreeLocalQuadraticCoefficient (m n : ℕ) : ℝ :=
  3 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * ((n : ℝ) - 2)

/-- A uniform bound for the absolute sizes of the three cubic terms. -/
noncomputable def orderThreeLocalCubicCoefficient (m n : ℕ) : ℝ :=
  4 + 3 * Real.sqrt ((m : ℝ) * n) + 6 * Real.sqrt ((m : ℝ) + n)

/-- A radius in squared cell energy, not an unnormalized entrywise distance. -/
noncomputable def orderThreeLocalEnergyRadius (m n : ℕ) : ℝ :=
  (orderThreeLocalQuadraticCoefficient m n / (2 * orderThreeLocalCubicCoefficient m n)) ^ 2

theorem orderThreeLocalQuadraticCoefficient_pos {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    0 < orderThreeLocalQuadraticCoefficient m n := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hmsub : (0 : ℝ) < m - 2 := by linarith
  have hnsub : (0 : ℝ) < n - 2 := by linarith
  exact mul_pos (mul_pos (mul_pos (by norm_num) (inv_pos.mpr (mul_pos hmpos hnpos))) hmsub) hnsub

theorem orderThreeLocalCubicCoefficient_pos (m n : ℕ) :
    0 < orderThreeLocalCubicCoefficient m n := by
  unfold orderThreeLocalCubicCoefficient
  positivity

theorem orderThreeLocalEnergyRadius_pos {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    0 < orderThreeLocalEnergyRadius m n := by
  exact sq_pos_of_pos (div_pos (orderThreeLocalQuadraticCoefficient_pos hm hn)
    (mul_pos (by norm_num) (orderThreeLocalCubicCoefficient_pos m n)))

/-- The mixed cubic is controlled by cell energy alone, with signed entries allowed. -/
theorem orderThree_mixed_lower_energy {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    -(Real.sqrt ((m : ℝ) * n) / 2 * Real.sqrt (orderThreeSquareSum X) *
      orderThreeSquareSum X) ≤ orderThreeMixedMoment X := by
  let E := orderThreeSquareSum X
  let T := orderThreeMarginalSquareSum X
  let A := orderThreeRowSquareSum X
  let B := orderThreeColSquareSum X
  let W : ℝ := (m : ℝ) * n
  have hE : 0 ≤ E := orderThreeSquareSum_nonneg X
  have hT : 0 ≤ T := orderThreeMarginalSquareSum_nonneg X
  have hA : 0 ≤ A := orderThreeRowSquareSum_nonneg X
  have hB : 0 ≤ B := orderThreeColSquareSum_nonneg X
  have hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have hTE : T ≤ E := orderThreeMarginalSquareSum_le hm hn X hX
  have hmixed := orderThree_mixed_sq_le hm hn X hX
  change orderThreeMixedMoment X ^ 2 ≤ (E - T) * A * B at hmixed
  have hmixed' : orderThreeMixedMoment X ^ 2 ≤ E * A * B := by
    nlinarith [mul_nonneg hT (mul_nonneg hA hB)]
  have hprod := orderThree_marginal_product_le hm hn X
  change 4 * A * B ≤ W * T ^ 2 at hprod
  have hT2 : T ^ 2 ≤ E ^ 2 := by nlinarith
  have hprodE := mul_le_mul_of_nonneg_left hprod hE
  have hT2E := mul_le_mul_of_nonneg_left hT2 (mul_nonneg hE hW)
  have hbound : 4 * orderThreeMixedMoment X ^ 2 ≤ W * E ^ 3 := by nlinarith
  have hroot : (Real.sqrt W / 2 * Real.sqrt E * E) ^ 2 = W * E ^ 3 / 4 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hW, Real.sq_sqrt hE]
    ring
  have hsq : orderThreeMixedMoment X ^ 2 ≤ (Real.sqrt W / 2 * Real.sqrt E * E) ^ 2 := by
    rw [hroot]
    nlinarith
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).1

theorem orderThree_linear_upper_energy {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (X : Board m n) (hX : totalMass X = 0) :
    orderThreeLinearMoment X ≤ Real.sqrt ((m : ℝ) + n) *
      Real.sqrt (orderThreeSquareSum X) * orderThreeSquareSum X := by
  have h := orderThree_linear_upper hm hn X
  have hTE := orderThreeMarginalSquareSum_le hm hn X hX
  have hsize : (0 : ℝ) ≤ (m : ℝ) + n := add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have hroot : Real.sqrt (((m : ℝ) + n) * orderThreeMarginalSquareSum X) ≤
      Real.sqrt ((m : ℝ) + n) * Real.sqrt (orderThreeSquareSum X) := by
    rw [← Real.sqrt_mul hsize]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTE hsize)
  exact h.trans (mul_le_mul_of_nonneg_right hroot (orderThreeSquareSum_nonneg X))

/-- The quadratic term dominates all cubic terms with an explicit energy error. -/
theorem orderThreeFailurePolynomial_local_energy_lower {m n : ℕ}
    (hm : 3 ≤ m) (hn : 3 ≤ n) {P : Board m n} (hP : IsProbability P) :
    (orderThreeLocalQuadraticCoefficient m n - orderThreeLocalCubicCoefficient m n *
      Real.sqrt (orderThreeSquareSum (orderThreeCentered P))) *
      orderThreeSquareSum (orderThreeCentered P) ≤
        orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let X := orderThreeCentered P
  let E := orderThreeSquareSum X
  have hX : totalMass X = 0 := orderThreeCentered_totalMass hm0 hn0 hP
  have hE : 0 ≤ E := orderThreeSquareSum_nonneg X
  have hcube : -Real.sqrt E * E ≤ ∑ i, ∑ j, X i j ^ 3 := by
    apply orderThree_cube_lower
    intro i j
    exact Real.neg_sqrt_le_of_sq_le (orderThree_entry_sq_le X i j)
  have hmixed := orderThree_mixed_lower_energy hm0 hn0 X hX
  have hlinear := orderThree_linear_upper_energy hm0 hn0 X hX
  have hr : 0 ≤ 6 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * orderThreeRowSquareSum X := by
    apply mul_nonneg _ (orderThreeRowSquareSum_nonneg X)
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr
      (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)))) (by linarith)
  have hc : 0 ≤ 6 * (((m : ℝ) * n)⁻¹) * ((n : ℝ) - 2) * orderThreeColSquareSum X := by
    apply mul_nonneg _ (orderThreeColSquareSum_nonneg X)
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr
      (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)))) (by linarith)
  have hexp := orderThreeFailurePolynomial_centered hm0 hn0 hP
  change orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) =
    orderThreeLocalQuadraticCoefficient m n * E +
    6 * (((m : ℝ) * n)⁻¹) * ((m : ℝ) - 2) * orderThreeRowSquareSum X +
    6 * (((m : ℝ) * n)⁻¹) * ((n : ℝ) - 2) * orderThreeColSquareSum X +
    4 * (∑ i, ∑ j, X i j ^ 3) + 6 * orderThreeMixedMoment X - 6 * orderThreeLinearMoment X at hexp
  change (orderThreeLocalQuadraticCoefficient m n - orderThreeLocalCubicCoefficient m n *
    Real.sqrt E) * E ≤ _
  unfold orderThreeLocalCubicCoefficient
  change -(Real.sqrt ((m : ℝ) * n) / 2 * Real.sqrt E * E) ≤ orderThreeMixedMoment X at hmixed
  change orderThreeLinearMoment X ≤ Real.sqrt ((m : ℝ) + n) * Real.sqrt E * E at hlinear
  nlinarith

/-- A closed, explicit neighborhood retains at least half the quadratic gap. -/
theorem orderThreeFailurePolynomial_local_lower {m n : ℕ}
    (hm : 3 ≤ m) (hn : 3 ≤ n) {P : Board m n} (hP : IsProbability P)
    (hnear : orderThreeSquareSum (orderThreeCentered P) ≤ orderThreeLocalEnergyRadius m n) :
    orderThreeLocalQuadraticCoefficient m n / 2 * orderThreeSquareSum (orderThreeCentered P) ≤
      orderThreeFailurePolynomial P - orderThreeFailurePolynomial (uniformBoard m n) := by
  have hC := orderThreeLocalCubicCoefficient_pos m n
  have hc := orderThreeLocalQuadraticCoefficient_pos hm hn
  have hden : 0 < 2 * orderThreeLocalCubicCoefficient m n := mul_pos (by norm_num) hC
  have hrad : 0 ≤ orderThreeLocalQuadraticCoefficient m n /
      (2 * orderThreeLocalCubicCoefficient m n) := (div_pos hc hden).le
  have hroot := (Real.sqrt_le_left hrad).mpr hnear
  have hscaled := (le_div_iff₀ hden).mp hroot
  have hcoef : orderThreeLocalQuadraticCoefficient m n / 2 ≤
      orderThreeLocalQuadraticCoefficient m n - orderThreeLocalCubicCoefficient m n *
        Real.sqrt (orderThreeSquareSum (orderThreeCentered P)) := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef (orderThreeSquareSum_nonneg _)).trans
    (orderThreeFailurePolynomial_local_energy_lower hm hn hP)

/-- The actual three-sample probability has a strict local uniform maximum in every dimension. -/
theorem exists_strict_local_separation_uniform {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : Board m n, IsProbability P → P ≠ uniformBoard m n →
      orderThreeSquareSum (orderThreeCentered P) ≤ ε →
      separationProbability P 3 < separationProbability (uniformBoard m n) 3 := by
  refine ⟨orderThreeLocalEnergyRadius m n, orderThreeLocalEnergyRadius_pos hm hn, ?_⟩
  intro P hP hPU hnear
  have hE : 0 < orderThreeSquareSum (orderThreeCentered P) := by
    have hnonneg := orderThreeSquareSum_nonneg (orderThreeCentered P)
    have hne : orderThreeSquareSum (orderThreeCentered P) ≠ 0 := by
      intro h
      exact hPU ((orderThreeCentered_eq_zero_iff P).mp ((orderThreeSquareSum_eq_zero_iff _).mp h))
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hgap := orderThreeFailurePolynomial_local_lower hm hn hP hnear
  have hpos := mul_pos (half_pos (orderThreeLocalQuadraticCoefficient_pos hm hn)) hE
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hPpoly := one_sub_separationProbability_three hP
  have hUpoly := one_sub_separationProbability_three (uniformBoard_isProbability hm0 hn0)
  linarith

end DittertRybin
