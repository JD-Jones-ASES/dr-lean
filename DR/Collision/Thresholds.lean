import DR.Collision.Concentration
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Explicit large-board thresholds

These are all-order inequalities for the exact binomial threshold, not a
finite numerical census. They control the dimension constants used in the
large-rectangle argument.
-/

namespace DittertRybin

private theorem self_le_choose_two {n : ℕ} (hn : 3 ≤ n) : n ≤ n.choose 2 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  norm_num [Nat.descFactorial, Nat.factorial] at h
  have hn1 : 2 ≤ n - 1 := by omega
  nlinarith

theorem collisionConstant_ge_square {k : ℕ} (hk : 4 ≤ k) :
    (k - 2) ^ 2 ≤ collisionConstant k := by
  have hA : k ≤ k.choose 2 := self_le_choose_two (by omega)
  have hA2 : k ≤ (k.choose 2) ^ 2 := by nlinarith
  have hC : (k.choose 2) ^ 2 ≤ ((k.choose 2) ^ 2).choose 2 :=
    self_le_choose_two (by omega)
  unfold collisionConstant
  rw [pow_two]
  exact Nat.mul_le_mul (by omega) (by omega)

theorem collisionConstant_le_tenth_power {k : ℕ} :
    (collisionConstant k : ℝ) ≤ (k : ℝ) ^ 10 / 64 := by
  have hA : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) 2 k)
  have hC : (((k.choose 2) ^ 2).choose 2 : ℝ) ≤ (k.choose 2 : ℝ) ^ 4 / 2 := by
    have h := Nat.choose_le_pow_div (α := ℝ) 2 ((k.choose 2) ^ 2)
    norm_num [Nat.cast_pow, ← pow_mul] at h
    exact h
  calc
    (collisionConstant k : ℝ) =
        (k.choose 2 : ℝ) * (((k.choose 2) ^ 2).choose 2 : ℝ) := by
      simp only [collisionConstant, Nat.cast_mul]
    _ ≤ (k.choose 2 : ℝ) * ((k.choose 2 : ℝ) ^ 4 / 2) := by gcongr
    _ ≤ ((k : ℝ) ^ 2 / 2) * (((k : ℝ) ^ 2 / 2) ^ 4 / 2) := by gcongr
    _ = _ := by ring

/-- The simple power threshold is sufficient for every sample order at least four. -/
theorem largeBoardThreshold_le_power {k : ℕ} (hk : 4 ≤ k) :
    largeBoardThreshold k ≤ k ^ 21 := by
  have hkR : (4 : ℝ) ≤ k := Nat.cast_le.mpr hk
  have hp : (64 : ℝ) ≤ (k : ℝ) ^ 10 := by
    calc
      64 ≤ (4 : ℝ) ^ 10 := by norm_num
      _ ≤ _ := by gcongr
  have hκ : (collisionConstant k : ℝ) + 1 ≤ (k : ℝ) ^ 10 / 32 := by
    have h := collisionConstant_le_tenth_power (k := k)
    linarith
  have hk2 : ((k - 2 : ℕ) : ℝ) ≤ k := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hD : (largeBoardThreshold k : ℝ) ≤ (k : ℝ) ^ 21 := by
    calc
      (largeBoardThreshold k : ℝ) =
          128 * ((k - 2 : ℕ) : ℝ) * ((collisionConstant k : ℝ) + 1) ^ 2 := by
        simp [largeBoardThreshold]
      _ ≤ 128 * (k : ℝ) * ((k : ℝ) ^ 10 / 32) ^ 2 := by gcongr
      _ = (k : ℝ) ^ 21 / 8 := by ring
      _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 21]
  exact_mod_cast hD

/-- At the explicit threshold, every contender meets the two smallness estimates. -/
theorem contender_smallness {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k)
    (hsize : largeBoardThreshold k ≤ min m n)
    (hcont : separationProbability (uniformBoard m n) k ≤ separationProbability P k) :
    normalizedVariance P < 1 / (128 * ((k - 2 : ℕ) : ℝ)) ∧
      peakMarginal P < 1 / (128 * ((k - 2 : ℕ) : ℝ) ^ 3) := by
  let t : ℝ := (k - 2 : ℕ)
  let κ : ℝ := collisionConstant k
  let d : ℝ := (min m n : ℕ)
  have ht : 0 < t := Nat.cast_pos.mpr (by omega)
  have hd : 0 < d := Nat.cast_pos.mpr (lt_min hm hn)
  have hκ : 0 ≤ κ := Nat.cast_nonneg _
  have hκ2 : t ^ 2 ≤ κ := by
    dsimp [t, κ]
    exact_mod_cast collisionConstant_ge_square hk
  have hD : 128 * t * (κ + 1) ^ 2 ≤ d := by
    have h := Nat.cast_le (α := ℝ).mpr hsize
    simpa [largeBoardThreshold, t, κ, d] using h
  have hcore : t ^ 2 * (κ + 2) ≤ (κ + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ2) (by linarith : 0 ≤ κ + 2)]
  have hscaled := mul_le_mul_of_nonneg_left hcore (show 0 ≤ 128 * t by positivity)
  have hηcross : (κ + 2) * (128 * t ^ 3) ≤ d := by nlinarith [hscaled]
  obtain ⟨hv, hη⟩ := contender_concentration hm hn hP hk hcont
  constructor
  · apply hv.trans_le
    apply (div_le_div_iff₀ hd (show 0 < 128 * t by positivity)).mpr
    nlinarith [hD]
  · apply hη.trans_le
    apply (div_le_div_iff₀ hd (show 0 < 128 * t ^ 3 by positivity)).mpr
    simpa using hηcross

end DittertRybin
