import DR.Certificates.SpectralEight
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Analytic dimension transfer of the spectral scalar gap

Concavity of the logarithm proves monotonicity of `(1+a/n)^n` whenever
the base is positive. The same lemma handles both the decreasing-bracket
power and the increasing permanent prefactor in the spectral comparison.
This transfers the proved dimension-eight scalar certificate to every
larger integer; it is not a finite dimension census.
-/

namespace DittertRybin.Certificates.SpectralTransfer

/-- The classical power sequence increases with its positive integer parameter.
The increment `a` may be negative, provided the smaller-parameter base is positive.
-/
theorem one_add_div_pow_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (a : ℝ)
    (ha : 0 < 1 + a / (m : ℝ)) :
    (1 + a / (m : ℝ)) ^ m ≤ (1 + a / (n : ℝ)) ^ n := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmn)
  have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hw0 : 0 ≤ (m : ℝ) / n := (div_pos hm0 hn0).le
  have hw1 : (m : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hmnR
  have hcomb : ((m : ℝ) / n) * (1 + a / m) + (1 - (m : ℝ) / n) * 1 =
      1 + a / n := by
    field_simp
    ring
  have hb : 0 < 1 + a / (n : ℝ) := by
    rw [← hcomb]
    exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hm0 hn0) ha)
      (mul_nonneg (sub_nonneg.mpr hw1) zero_le_one)
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 ha (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    hw0 (sub_nonneg.mpr hw1) (by ring : (m : ℝ) / n + (1 - (m : ℝ) / n) = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, hcomb] at hc
  have hlog := mul_le_mul_of_nonneg_left hc hn0.le
  have hcancel : (n : ℝ) * ((m : ℝ) / n * Real.log (1 + a / m)) =
      (m : ℝ) * Real.log (1 + a / m) := by
    field_simp
  rw [hcancel] at hlog
  apply (Real.log_le_log_iff (pow_pos ha m) (pow_pos hb n)).mp
  simpa only [Real.log_pow] using hlog

/-- The permanent prefactor is at least its exact dimension-eight value. -/
theorem prefactor_ge_eight {n : ℕ} (hn : 8 ≤ n) :
    (8 / 7 : ℝ) ^ 7 ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) := by
  have h := one_add_div_pow_mono (m := 7) (n := n - 1) (by decide) (by omega)
    (1 : ℝ) (by norm_num)
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_sub hn1, Nat.cast_one] at h
  have hd : (n : ℝ) - 1 ≠ 0 := by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he : (1 : ℝ) + 1 / ((n : ℝ) - 1) = (n : ℝ) / ((n : ℝ) - 1) := by field_simp; ring
  rw [he] at h
  norm_num at h ⊢
  exact h

/-- The fixed rational loss in the dimension-eight certificate. -/
noncomputable def baseLoss (z : ℝ) : ℝ := (7 / 50 : ℝ) * z + (73 / 1000 : ℝ) * (1 - z ^ 2)

theorem baseLoss_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ baseLoss z := by
  have hs : 0 ≤ 1 - z ^ 2 := by nlinarith
  exact add_nonneg (mul_nonneg (by norm_num) hz) (mul_nonneg (by norm_num) hs)

theorem baseLoss_le {z : ℝ} (hz1 : z ≤ 1) : baseLoss z ≤ 213 / 1000 := by
  dsimp [baseLoss]
  nlinarith [sq_nonneg z]

theorem scaled_bracket_pos {n : ℕ} (hn : 8 ≤ n) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < 1 - 8 * baseLoss z / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 8) hn)
  have hn8 : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hfrac : 8 * baseLoss z / (n : ℝ) ≤ baseLoss z := by
    apply (div_le_iff₀ hn0).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hn8 (baseLoss_nonneg hz hz1)
  have hbase := baseLoss_le hz1
  linarith

theorem bracket_power_ge_eight {n : ℕ} (hn : 8 ≤ n) {z : ℝ} (hz1 : z ≤ 1) :
    (1 - baseLoss z) ^ 8 ≤ (1 - 8 * baseLoss z / (n : ℝ)) ^ n := by
  have hbase := baseLoss_le hz1
  have ha : 0 < 1 + (-8 * baseLoss z) / (8 : ℝ) := by linarith
  have h := one_add_div_pow_mono (by decide : 0 < 8) hn (-8 * baseLoss z) ha
  norm_num only [Nat.cast_ofNat] at h
  have he : 1 + (-8 * baseLoss z) / (8 : ℝ) = 1 - baseLoss z := by ring
  have he' : 1 + (-8 * baseLoss z) / (n : ℝ) = 1 - 8 * baseLoss z / (n : ℝ) := by ring
  rwa [he, he'] at h

/-- The certified scalar contradiction transfers to every integer dimension at least eight. -/
theorem scaled_gap_pos {n : ℕ} (hn : 8 ≤ n) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) *
      (1 - 8 * baseLoss z / (n : ℝ)) ^ n := by
  have hb : 0 < 1 - baseLoss z := by have h := baseLoss_le hz1; linarith
  have hpref : 0 ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) := by
    have hnR : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
    exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith)) _
  calc
    1 - z ^ 2 < (8 / 7 : ℝ) ^ 7 * (1 - baseLoss z) ^ 8 := by
      convert sub_pos.mp (SpectralEight.gap_pos z hz hz1) using 1
      dsimp [baseLoss]
      ring
    _ ≤ _ := mul_le_mul (prefactor_ge_eight hn) (bracket_power_ge_eight hn hz1)
      (pow_nonneg hb.le _) hpref

/-- Any actual spectral parameters below the scaled rational caps give the same contradiction. -/
theorem gap_pos_of_parameter_bounds {n : ℕ} (hn : 8 ≤ n) (a b z : ℝ)
    (ha : a ≤ (8 * (7 / 50 : ℝ)) / n) (hb : b ≤ (8 * (73 / 1000 : ℝ)) / n)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) *
      (1 - a * z - b * (1 - z ^ 2)) ^ n := by
  have hs : 0 ≤ 1 - z ^ 2 := by nlinarith
  have haz := mul_le_mul_of_nonneg_right ha hz
  have hbz := mul_le_mul_of_nonneg_right hb hs
  have hsplit : 8 * baseLoss z / (n : ℝ) =
      ((8 * (7 / 50 : ℝ)) / n) * z + ((8 * (73 / 1000 : ℝ)) / n) * (1 - z ^ 2) := by
    dsimp [baseLoss]
    ring
  have hbracket : 1 - 8 * baseLoss z / (n : ℝ) ≤ 1 - a * z - b * (1 - z ^ 2) := by
    rw [hsplit]
    linarith
  have hpow := pow_le_pow_left₀ (scaled_bracket_pos hn hz hz1).le hbracket n
  have hpref : 0 ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) := by
    have hnR : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
    exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith)) _
  exact (scaled_gap_pos hn z hz hz1).trans_le (mul_le_mul_of_nonneg_left hpow hpref)

end DittertRybin.Certificates.SpectralTransfer
