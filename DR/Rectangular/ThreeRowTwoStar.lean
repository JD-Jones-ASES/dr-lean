import DR.Rectangular.ThreeRowCubic
import DR.Rectangular.OrderThreeLargeExpansion

/-! Exact value and strict uniform comparison for the actual two-star support. -/
namespace DittertRybin
open scoped BigOperators

/-- One row occupies every column except b; the other two rows occupy only b. -/
def threeRowTwoStar {n : ℕ} (i : Fin 3) (b : Fin n) (u : ℝ) : Board 3 n :=
  fun r c => if r = i then (if c = b then 0 else u) else (if c = b then u else 0)

private theorem sum_column_two_value {n : ℕ} (b : Fin n) (x y : ℝ) :
    (∑ j : Fin n, if j = b then x else y) = x + ((n : ℝ)-1)*y := by
  have h (j : Fin n) : (if j = b then x else y) = y + if j = b then x-y else 0 := by
    by_cases hj : j = b <;> simp [hj]
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem rowSum_threeRowTwoStar {n : ℕ} (i r : Fin 3) (b : Fin n) (u : ℝ) :
    rowSum (threeRowTwoStar i b u) r = if r = i then ((n : ℝ)-1)*u else u := by
  by_cases hr : r = i <;>
    simp only [rowSum, threeRowTwoStar, hr, if_true, if_false] <;>
    rw [sum_column_two_value] <;> ring

theorem colSum_threeRowTwoStar {n : ℕ} (i : Fin 3) (b c : Fin n) (u : ℝ) :
    colSum (threeRowTwoStar i b u) c = if c = b then 2*u else u := by
  fin_cases i <;> by_cases hc : c = b <;>
    simp [colSum, threeRowTwoStar, hc, Fin.sum_univ_succ] <;> ring

theorem totalMass_threeRowTwoStar {n : ℕ} (i : Fin 3) (b : Fin n) (u : ℝ) :
    totalMass (threeRowTwoStar i b u) = ((n : ℝ)+1)*u := by
  simp only [totalMass, rowSum_threeRowTwoStar]
  fin_cases i <;> simp [Fin.sum_univ_succ] <;> ring

theorem threeRowPair_twoStar {n : ℕ} (i r : Fin 3) (b : Fin n) (u : ℝ) :
    threeRowPair (threeRowTwoStar i b u) r = if r = i then u^2 else 0 := by
  fin_cases i <;> fin_cases r <;>
    simp [threeRowPair, threeRowTwoStar, mul_ite, ite_mul, pow_two]
  all_goals
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = b <;> simp [hj]

theorem threeRowTwoStar_column_moment {n : ℕ} (i : Fin 3) (b : Fin n) (u : ℝ) (k : ℕ) :
    (∑ j, colSum (threeRowTwoStar i b u) j ^ k) =
      (2*u)^k + ((n : ℝ)-1)*u^k := by
  simp only [colSum_threeRowTwoStar, ite_pow]
  exact sum_column_two_value b _ _

theorem separationProbability_threeRowTwoStar {n : ℕ} (i : Fin 3) (b : Fin n) (u : ℝ) :
    separationProbability (threeRowTwoStar i b u) 3 =
      (n : ℝ)*(n-1)*(n+1)*u^3 := by
  rw [separationProbability_threeRow_cubic, threeRowSuccessPolynomial_grouped,
    totalMass_threeRowTwoStar, threeRowTwoStar_column_moment, threeRowTwoStar_column_moment]
  have hp : (∑ r, rowSum (threeRowTwoStar i b u) r *
      threeRowPair (threeRowTwoStar i b u) r) = ((n : ℝ)-1)*u^3 := by
    simp only [rowSum_threeRowTwoStar, threeRowPair_twoStar]
    fin_cases i <;> simp <;> ring
  have ht : (∑ j, threeRowTwoStar i b u 0 j * threeRowTwoStar i b u 1 j *
      threeRowTwoStar i b u 2 j) = 0 := by
    fin_cases i <;> simp [threeRowTwoStar, mul_ite, ite_mul]
    all_goals
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j = b <;> simp [hj]
  rw [hp, ht]
  ring


theorem uniformSeparationValue_three_rows {n : ℕ} (hn : 0 < n) :
    uniformSeparationValue 3 n 3 = 1 - 7 / (3*(n : ℝ)) + 14 / (9*(n : ℝ)^2) := by
  have h := one_sub_separationProbability_three (uniformBoard_isProbability (m := 3) (by decide) hn)
  rw [separationProbability_uniform (by decide) hn,
    orderThreeFailurePolynomial_uniform (by decide) hn] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : uniformSeparationValue 3 n 3 =
      1 - (9 * ((3 : ℝ)*n)⁻¹ - 6*((3 : ℝ)*n)⁻¹*(3⁻¹+(n : ℝ)⁻¹) +
        4*(((3 : ℝ)*n)⁻¹)^2) := by linarith
  rw [he]
  field_simp
  ring

theorem separationProbability_threeRowTwoStar_normalized {n : ℕ}
    (i : Fin 3) (b : Fin n) (u : ℝ)
    (hmass : totalMass (threeRowTwoStar i b u) = 1) :
    separationProbability (threeRowTwoStar i b u) 3 =
      (n : ℝ)*(n-1)/(n+1)^2 := by
  rw [totalMass_threeRowTwoStar] at hmass
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  have hu : u = 1/((n : ℝ)+1) := by
    apply (eq_div_iff hn1).mpr
    nlinarith
  rw [separationProbability_threeRowTwoStar, hu]
  field_simp

/-- The complete exact gap to uniform; its factors explain the dimension-two boundary. -/
theorem threeRowTwoStar_uniform_gap {n : ℕ} (hn : 0 < n)
    (i : Fin 3) (b : Fin n) (u : ℝ)
    (hmass : totalMass (threeRowTwoStar i b u) = 1) :
    uniformSeparationValue 3 n 3 - separationProbability (threeRowTwoStar i b u) 3 =
      ((n : ℝ)-2)*(6*(n : ℝ)^2-7*n-7)/(9*(n : ℝ)^2*((n : ℝ)+1)^2) := by
  rw [uniformSeparationValue_three_rows hn, separationProbability_threeRowTwoStar_normalized i b u hmass]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- Every normalized two-star board is strictly worse than uniform when n≥3. -/
theorem separationProbability_threeRowTwoStar_lt_uniform {n : ℕ} (hn : 3 ≤ n)
    (i : Fin 3) (b : Fin n) (u : ℝ)
    (hmass : totalMass (threeRowTwoStar i b u) = 1) :
    separationProbability (threeRowTwoStar i b u) 3 < uniformSeparationValue 3 n 3 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ (n : ℝ)*((n : ℝ)-3) := mul_nonneg (by positivity) (by linarith)
  have hq : 0 < 6*(n : ℝ)^2-7*n-7 := by nlinarith
  apply sub_pos.mp
  rw [threeRowTwoStar_uniform_gap (by omega) i b u hmass]
  exact div_pos (mul_pos (by linarith) hq) (by positivity)

end DittertRybin
