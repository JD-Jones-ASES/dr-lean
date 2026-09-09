import DR.Rectangular.ThreeRowInterpolation
import DR.Rectangular.ThreeRowSupportNormal
import DR.Rectangular.ThreeRowLocal

/-!
# Every positive global three-sample maximizer is uniform

The actual cubic is constant on a line joining two positive global maximizers:
its two endpoint values coincide and both endpoint derivatives vanish. Strict
local uniqueness then identifies the original maximizer, on every rectangle
whose dimensions are independently at least three.
-/

namespace DittertRybin
open scoped BigOperators

/-- Interior stationarity in every mass-zero direction, including signed directions. -/
theorem IsSeparationGlobalMax.gradient_dot_zero_of_positive {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P) (hpos : ∀ i j, 0 < P i j)
    (D : Board m n) (hD : totalMass D = 0) :
    (∑ i, ∑ j, separationGradient P k i j * D i j) = 0 := by
  have hg (i : Fin m) (j : Fin n) := hmax.gradient_eq_value hP (i, j) (hpos i j)
  simp only [hg, ← Finset.mul_sum]
  change (k : ℝ) * separationProbability P k * totalMass D = 0
  rw [hD, mul_zero]

/-- The genuine three-sample cubic is flat between any two positive global maximizers. -/
theorem separationProbability_three_segment_flat {m n : ℕ} {P Q : Board m n}
    (hP : IsProbability P) (hQ : IsProbability Q)
    (hmaxP : IsSeparationGlobalMax P 3) (hmaxQ : IsSeparationGlobalMax Q 3)
    (hposP : ∀ i j, 0 < P i j) (hposQ : ∀ i j, 0 < Q i j) (t : ℝ) :
    separationProbability (fun i j => (1 - t) * P i j + t * Q i j) 3 =
      separationProbability P 3 := by
  have hD : totalMass (fun i j => Q i j - P i j) = 0 := by
    simp only [totalMass, rowSum, Finset.sum_sub_distrib]
    change totalMass Q - totalMass P = 0
    rw [hQ.2, hP.2, sub_self]
  have hdP := hmaxP.gradient_dot_zero_of_positive hP hposP _ hD
  have hdQ := hmaxQ.gradient_dot_zero_of_positive hQ hposQ _ hD
  have hv : separationProbability Q 3 = separationProbability P 3 :=
    le_antisymm (hmaxP Q hQ) (hmaxQ P hP)
  rw [separationProbability_three_hermite, hdP, hdQ, hv]
  ring

/-- A convex combination stays in the complete matrix probability simplex. -/
theorem probability_convex_combination {m n : ℕ} {P Q : Board m n}
    (hP : IsProbability P) (hQ : IsProbability Q) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbability (fun i j => (1 - t) * P i j + t * Q i j) := by
  constructor
  · intro i j
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hP.1 i j)) (mul_nonneg ht (hQ.1 i j))
  · simp only [totalMass, rowSum, Finset.sum_add_distrib, ← Finset.mul_sum]
    change (1 - t) * totalMass P + t * totalMass Q = 1
    rw [hP.2, hQ.2]
    ring

theorem orderThreeCentered_squareSum_segment {m n : ℕ} (P : Board m n) (t : ℝ) :
    orderThreeSquareSum (orderThreeCentered
      (fun i j => (1 - t) * uniformBoard m n i j + t * P i j)) =
        t ^ 2 * orderThreeSquareSum (orderThreeCentered P) := by
  have he (i : Fin m) (j : Fin n) :
      orderThreeCentered (fun i j => (1 - t) * uniformBoard m n i j + t * P i j) i j =
        t * orderThreeCentered P i j := by
    unfold orderThreeCentered
    ring
  simp only [orderThreeSquareSum, he, mul_pow, ← Finset.mul_sum]

/-- Exact positive-case uniqueness; neither an aspect-ratio bound nor a size threshold is imposed. -/
theorem IsSeparationGlobalMax.eq_uniform_of_positive_three {m n : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (hm : 3 ≤ m) (hn : 3 ≤ n) (hpos : ∀ i j, 0 < P i j) : P = uniformBoard m n := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hU := uniformBoard_isProbability hm0 hn0
  have hUpos (i : Fin m) (j : Fin n) : 0 < uniformBoard m n i j := by
    exact inv_pos.mpr (mul_pos (Nat.cast_pos.mpr hm0) (Nat.cast_pos.mpr hn0))
  have hUmax := hmax.uniform_of_positive hP (by norm_num : 2 ≤ 3) hm0 hn0 hpos
  by_contra hne
  obtain ⟨ε, hε, hlocal⟩ := exists_strict_local_separation_uniform hm hn
  let E := orderThreeSquareSum (orderThreeCentered P)
  have hE : 0 ≤ E := orderThreeSquareSum_nonneg _
  let t : ℝ := min (1 / 2) (ε / (E + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htε : t * (E + 1) ≤ ε := (le_div_iff₀ (by linarith : 0 < E + 1)).mp (min_le_right _ _)
  have hsmall : t ^ 2 * E ≤ ε := by
    have hs := mul_nonneg ht.le (sub_nonneg.mpr ht1)
    have he := mul_le_mul_of_nonneg_right (show t ^ 2 ≤ t by nlinarith only [hs]) hE
    nlinarith only [he, htε, ht]
  let R : Board m n := fun i j => (1 - t) * uniformBoard m n i j + t * P i j
  have hR : IsProbability R := probability_convex_combination hU hP ht.le ht1
  have hRne : R ≠ uniformBoard m n := by
    intro heq
    apply hne
    ext i j
    have hij := congrFun (congrFun heq i) j
    change (1 - t) * uniformBoard m n i j + t * P i j = uniformBoard m n i j at hij
    have hz : t * (P i j - uniformBoard m n i j) = 0 := by linarith only [hij]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt ht))
  have hRsmall : orderThreeSquareSum (orderThreeCentered R) ≤ ε := by
    rw [orderThreeCentered_squareSum_segment]
    exact hsmall
  have hstrict := hlocal R hR hRne hRsmall
  have hflat := separationProbability_three_segment_flat hU hP hUmax hmax hUpos hpos t
  exact (ne_of_lt hstrict) hflat

end DittertRybin
