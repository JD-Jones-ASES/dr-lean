import DR.Square.AlternatingPath

/-! The exact ten-vertex alternating path for the remaining square order-five argument. -/

namespace DittertRybin

open scoped BigOperators

private theorem sum_four (f : Fin 4 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3))) = _
  ring

private theorem sum_five (f : Fin 5 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4)))) = _
  ring

private theorem sum_nine (f : Fin 9 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8)))))))) = _
  ring

private theorem sum_ten (f : Fin 10 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9))))))))) = _
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alternating_ten_gram_identity (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (v : Fin 9 → ℝ) :
    (∑ i, (∑ j, weightedPathIncidence (alternatingWeights 9 q b) i j * v j) ^ 2) =
      2 * q * (∑ i, (![v 0, v 2, v 4, v 6, v 8] : Fin 5 → ℝ) i ^ 2) +
      2 * b * (∑ j, (![v 1, v 3, v 5, v 7] : Fin 4 → ℝ) j ^ 2) -
      2 * (Real.sqrt q * Real.sqrt b) *
        (∑ i, (![v 0, v 2, v 4, v 6, v 8] : Fin 5 → ℝ) i *
          joinFive ![v 1, v 3, v 5, v 7] i) := by
  rw [sum_ten]
  norm_num [-Fin.val_eq_zero_iff, weightedPathIncidence, alternatingWeights, joinFive, sum_ten, sum_nine,
    sum_five, sum_four, Fin.ext_iff]
  dsimp
  ring_nf
  simp [Real.sq_sqrt hq, Real.sq_sqrt hb]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alternating_ten_range (q b : ℝ) (hq : 0 < q) (hb : 0 < b)
    (f : Fin 10 → ℝ) (hf : ∑ i, f i = 0) :
    ∃ v : Fin 9 → ℝ, ∀ i,
      f i = ∑ j, weightedPathIncidence (alternatingWeights 9 q b) i j * v j := by
  refine ⟨![(f 0) / Real.sqrt q,
    (f 0 + f 1) / Real.sqrt b,
    (f 0 + f 1 + f 2) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8) / Real.sqrt q], ?_⟩
  have hq0 := (Real.sqrt_pos.mpr hq).ne'
  have hb0 := (Real.sqrt_pos.mpr hb).ne'
  rw [sum_ten] at hf
  intro i
  fin_cases i <;>
    norm_num [-Fin.val_eq_zero_iff, weightedPathIncidence, alternatingWeights, sum_nine, Fin.ext_iff,
      mul_div_cancel₀, hq0, hb0] <;> dsimp <;>
      field_simp [hq0, hb0] <;> nlinarith

theorem alternating_ten_gram_strict (q b h : ℝ) (hq : 0 < q) (hh : 0 ≤ h)
    (hhq : h < q * (19 / 100)) (hb : alternatingBoundary q h (19 / 100) < b)
    (v : Fin 9 → ℝ) (hv : v ≠ 0) :
    h * (∑ j, v j ^ 2) <
      ∑ i, (∑ j, weightedPathIncidence (alternatingWeights 9 q b) i j * v j) ^ 2 := by
  have hden : 0 < 2 * (q * (19 / 100) - h) := by linarith
  have hq2 : 0 < 2 * q - h := by linarith
  have hB0 : 0 ≤ alternatingBoundary q h (19 / 100) :=
    div_nonneg (mul_nonneg hh hq2.le) hden.le
  have hb0 : 0 < b := lt_of_le_of_lt hB0 hb
  have hmul := (div_lt_iff₀ hden).mp hb
  have hcsq : (Real.sqrt q * Real.sqrt b) ^ 2 = q * b := by
    rw [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hb0.le]
  have hschur : (Real.sqrt q * Real.sqrt b) ^ 2 * (181 / 50) < (2 * q - h) * (2 * b - h) := by
    rw [hcsq]
    nlinarith
  have hvpos : 0 < ∑ j, v j ^ 2 := by
    have hex : ∃ j, v j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    obtain ⟨j, hj⟩ := hex
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hj)
      (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  have hsplit : (∑ j, v j ^ 2) =
      (∑ i, (![v 0, v 2, v 4, v 6, v 8] : Fin 5 → ℝ) i ^ 2) +
      ∑ j, (![v 1, v 3, v 5, v 7] : Fin 4 → ℝ) j ^ 2 := by
    norm_num [sum_nine, sum_five, sum_four]; dsimp; ring
  have hstrict := strict_schur_sum ![v 0, v 2, v 4, v 6, v 8]
    ![v 1, v 3, v 5, v 7] (joinFive ![v 1, v 3, v 5, v 7])
    (2 * q - h) (2 * b - h) (Real.sqrt q * Real.sqrt b) (181 / 50)
    hq2 hschur (joinFive_bound _) (by rwa [← hsplit])
  rw [alternating_ten_gram_identity q b hq.le hb0.le, hsplit]
  nlinarith

/-- Strict coercivity at any h below the inversion threshold, proved through finite Gram algebra. -/
theorem alternating_ten_strict (q b h : ℝ) (hq : 0 < q) (hh : 0 ≤ h)
    (hhq : h < q * (19 / 100)) (hb : alternatingBoundary q h (19 / 100) < b)
    (f : Fin 10 → ℝ) (hf : ∑ i, f i = 0) (hf0 : 0 < ∑ i, f i ^ 2) :
    h * (∑ i, f i ^ 2) < ∑ j, alternatingWeights 9 q b j * sweepGap f j ^ 2 := by
  have hden : 0 < 2 * (q * (19 / 100) - h) := by linarith
  have hq2 : 0 < 2 * q - h := by linarith
  have hB0 : 0 ≤ alternatingBoundary q h (19 / 100) :=
    div_nonneg (mul_nonneg hh hq2.le) hden.le
  have hb0 : 0 < b := lt_of_le_of_lt hB0 hb
  have hw (j : Fin 9) : 0 ≤ alternatingWeights 9 q b j := by
    unfold alternatingWeights; split <;> positivity
  have h := incidence_strict_bound_transfer (weightedPathIncidence (alternatingWeights 9 q b)) h
    (alternating_ten_gram_strict q b h hq hh hhq hb) f hf0 (alternating_ten_range q b hq hb0 f hf)
  rwa [weightedPathIncidence_energy _ hw] at h

end DittertRybin
