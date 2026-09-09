import DR.Certificates.SpectralTransfer
import DR.Certificates.SpectralSeven
import DR.Square.Contenders

/-!
# Exact caps for the gamma-based spectral parameters

The factorial ratio and Bernoulli's inequality give `gamma(n+1) ≤ gamma(n)/2`.
For n≥8 the cubic polynomial weights used in both spectral numerators grow
by at most two. Consequently the weighted numerators decrease, while the
positive denominator `1-gamma(n)` increases. Exact arithmetic at eight then
supplies the rational parameter caps needed by `SpectralTransfer`.
-/

namespace DittertRybin.Certificates.SpectralParameters

theorem gamma_succ {n : ℕ} (hn : 0 < n) :
    dittertConstant (n + 1) = dittertConstant n * ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs0 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [dittertConstant, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    div_pow, pow_succ]
  field_simp

/-- A genuine factorial-ratio bound, valid for every positive dimension. -/
theorem gamma_succ_le_half {n : ℕ} (hn : 0 < n) :
    dittertConstant (n + 1) ≤ dittertConstant n / 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 := hnR.ne'
  have hs0 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hb := one_add_mul_le_pow (a := 1 / (n : ℝ)) (by linarith [one_div_pos.mpr hnR]) n
  have hb' : (2 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ n := by
    norm_num [hn0] at hb ⊢
    exact hb
  have hq : 0 ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by positivity
  have hi : ((n : ℝ) / ((n : ℝ) + 1)) ^ n * (1 + 1 / (n : ℝ)) ^ n = 1 := by
    rw [← mul_pow]
    have he : (n : ℝ) / ((n : ℝ) + 1) * (1 + 1 / (n : ℝ)) = 1 := by field_simp
    rw [he, one_pow]
  have h := mul_le_mul_of_nonneg_left hb' hq
  rw [hi] at h
  have hhalf : ((n : ℝ) / ((n : ℝ) + 1)) ^ n ≤ 1 / 2 := by linarith
  rw [gamma_succ hn]
  have hγ := dittertConstant_pos hn
  have hmul := mul_le_mul_of_nonneg_left hhalf hγ.le
  linarith

theorem gamma_succ_le {n : ℕ} (hn : 0 < n) : dittertConstant (n + 1) ≤ dittertConstant n := by
  have h := gamma_succ_le_half hn
  have hp := dittertConstant_pos hn
  linarith

theorem polynomial_weight_growth {x : ℝ} (hx : 8 ≤ x) :
    (x + 1) ^ 3 ≤ 2 * x ^ 3 ∧
      (x + 1) ^ 2 * (2 * (x + 1) - 1) ≤ 2 * (x ^ 2 * (2 * x - 1)) := by
  have hx0 : 0 ≤ x := by linarith
  have h2 := mul_nonneg hx0 (sub_nonneg.mpr hx)
  have h3 := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)
  constructor <;> nlinarith

theorem cube_gamma_succ_le {n : ℕ} (hn : 8 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ 3 * dittertConstant (n + 1) ≤
      (n : ℝ) ^ 3 * dittertConstant n := by
  have hnR : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hγ := dittertConstant_pos (by omega : 0 < n)
  have hhalf := gamma_succ_le_half (by omega : 0 < n)
  have hgrowth := (polynomial_weight_growth hnR).1
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((n : ℝ) + 1) ^ 3 * (dittertConstant n / 2) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hgrowth hγ.le]

theorem sweep_gamma_succ_le {n : ℕ} (hn : 8 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ 2 * (2 * ((n + 1 : ℕ) : ℝ) - 1) * dittertConstant (n + 1) ≤
      (n : ℝ) ^ 2 * (2 * (n : ℝ) - 1) * dittertConstant n := by
  have hnR : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hγ := dittertConstant_pos (by omega : 0 < n)
  have hhalf := gamma_succ_le_half (by omega : 0 < n)
  have hgrowth := (polynomial_weight_growth hnR).2
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 1)) * (dittertConstant n / 2) :=
      mul_le_mul_of_nonneg_left hhalf (mul_nonneg (sq_nonneg _) (by linarith))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hgrowth hγ.le]

theorem gamma_le_eight {n : ℕ} (hn : 8 ≤ n) : dittertConstant n ≤ dittertConstant 8 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (gamma_succ_le (by omega)).trans ih

theorem cube_gamma_le_eight {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) ^ 3 * dittertConstant n ≤ (8 : ℝ) ^ 3 * dittertConstant 8 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (cube_gamma_succ_le hn).trans ih

theorem sweep_gamma_le_eight {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) ^ 2 * (2 * (n : ℝ) - 1) * dittertConstant n ≤
      (8 : ℝ) ^ 2 * (2 * (8 : ℝ) - 1) * dittertConstant 8 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (sweep_gamma_succ_le hn).trans ih

/-- The actual square-root parameter from the entropy discrepancy estimate. -/
noncomputable def rootParameter (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * dittertConstant n / (1 - dittertConstant n))

/-- The actual unrefined sweep parameter from the square argument. -/
noncomputable def sweepParameter (n : ℕ) : ℝ :=
  (n : ℝ) * (2 * (n : ℝ) - 1) * dittertConstant n / (4 * (1 - dittertConstant n))

theorem rootParameter_le_scaled_cap {n : ℕ} (hn : 8 ≤ n) :
    rootParameter n ≤ (8 * (7 / 50 : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hγ := dittertConstant_pos (by omega : 0 < n)
  have hd : 0 < 1 - dittertConstant n := sub_pos.mpr (dittertConstant_lt_one (by omega))
  have hd8 : 0 < 1 - dittertConstant 8 := sub_pos.mpr (dittertConstant_lt_one (by decide))
  have hnum8 : 0 ≤ (8 : ℝ) ^ 3 * dittertConstant 8 :=
    mul_nonneg (by norm_num) (dittertConstant_pos (by decide)).le
  have hbound := div_le_div₀ hnum8 (cube_gamma_le_eight hn) hd8
    (sub_le_sub_left (gamma_le_eight hn) 1)
  have hbase : (8 : ℝ) ^ 3 * dittertConstant 8 / (1 - dittertConstant 8) <
      (8 * (7 / 50 : ℝ)) ^ 2 := by norm_num [dittertConstant, Nat.factorial]
  have hsqrt : ((n : ℝ) * rootParameter n) ^ 2 =
      (n : ℝ) ^ 3 * dittertConstant n / (1 - dittertConstant n) := by
    rw [mul_pow, rootParameter, Real.sq_sqrt (div_nonneg (mul_nonneg hn0.le hγ.le) hd.le)]
    ring
  apply (le_div_iff₀ hn0).mpr
  nlinarith

theorem sweepParameter_le_scaled_cap {n : ℕ} (hn : 8 ≤ n) :
    sweepParameter n ≤ (8 * (73 / 1000 : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hd8 : 0 < 1 - dittertConstant 8 := sub_pos.mpr (dittertConstant_lt_one (by decide))
  have hnum8 : 0 ≤ (8 : ℝ) ^ 2 * (2 * (8 : ℝ) - 1) * dittertConstant 8 :=
    mul_nonneg (by norm_num) (dittertConstant_pos (by decide)).le
  have hbound := div_le_div₀ hnum8 (sweep_gamma_le_eight hn) hd8
    (sub_le_sub_left (gamma_le_eight hn) 1)
  have hbase : (8 : ℝ) ^ 2 * (2 * (8 : ℝ) - 1) * dittertConstant 8 /
      (1 - dittertConstant 8) < 4 * (8 * (73 / 1000 : ℝ)) := by
    norm_num [dittertConstant, Nat.factorial]
  have hscale : 4 * ((n : ℝ) * sweepParameter n) =
      (n : ℝ) ^ 2 * (2 * (n : ℝ) - 1) * dittertConstant n / (1 - dittertConstant n) := by
    have hd : 1 - dittertConstant n ≠ 0 :=
      (sub_pos.mpr (dittertConstant_lt_one (by omega : 2 ≤ n))).ne'
    unfold sweepParameter
    field_simp
  apply (le_div_iff₀ hn0).mpr
  nlinarith

/-- Full dimension transfer for the concrete gamma-based spectral parameters. -/
theorem spectral_gap_pos {n : ℕ} (hn : 8 ≤ n) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) *
      (1 - rootParameter n * z - sweepParameter n * (1 - z ^ 2)) ^ n :=
  SpectralTransfer.gap_pos_of_parameter_bounds hn _ _ z
    (rootParameter_le_scaled_cap hn) (sweepParameter_le_scaled_cap hn) hz hz1

/-- Reciprocal form of the exact factorial-ratio power. -/
theorem gamma_ratio_power_inv {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) / ((n : ℝ) + 1)) ^ n = 1 / (1 + 1 / (n : ℝ)) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 := hnR.ne'
  have hs0 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [one_div, ← inv_pow]
  congr 1
  field_simp

/-- Consecutive gamma ratios decrease, proved using the same logarithmic-concavity lemma. -/
theorem gamma_ratio_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    dittertConstant (n + 1) * dittertConstant m ≤
      dittertConstant n * dittertConstant (m + 1) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp := SpectralTransfer.one_add_div_pow_mono hm hmn (1 : ℝ) (by positivity)
  have hp0 : 0 < (1 + 1 / (m : ℝ)) ^ m := by positivity
  have hi := one_div_le_one_div_of_le hp0 hp
  rw [← gamma_ratio_power_inv hn, ← gamma_ratio_power_inv hm] at hi
  rw [gamma_succ hn, gamma_succ hm]
  have hmul := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (dittertConstant_pos hn).le (dittertConstant_pos hm).le)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The symmetric gamma product has its minimum at a one-dimensional endpoint. -/
theorem gamma_product_endpoint {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    dittertConstant (s + t - 1) ≤ dittertConstant s * dittertConstant t := by
  have H : ∀ s : ℕ, 1 ≤ s → ∀ t : ℕ, s ≤ t →
      dittertConstant (s + t - 1) ≤ dittertConstant s * dittertConstant t := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
        intro t ht
        have hγ1 : dittertConstant 1 = 1 := by norm_num [dittertConstant]
        rw [hγ1, one_mul, show 1 + t - 1 = t by omega]
    | succ s hs ih =>
        intro t hst
        have hrec := ih (t + 1) (by omega)
        have hratio := gamma_ratio_antitone (m := s) (n := t) (by omega) (by omega)
        have he : s + (t + 1) - 1 = (s + 1) + t - 1 := by omega
        rw [he] at hrec
        exact hrec.trans (by simpa only [mul_comm] using hratio)
  rcases le_total s t with hst | hts
  · exact H s hs t hst
  · simpa only [Nat.add_comm, mul_comm] using H t ht s hts

/-- The actual two-block permanent constant dominates the endpoint constant. -/
theorem gamma_split_ge_predecessor {n s : ℕ} (hs : 1 ≤ s) (hsn : s < n) :
    dittertConstant (n - 1) ≤ dittertConstant s * dittertConstant (n - s) := by
  have h := gamma_product_endpoint hs (by omega : 0 < n - s)
  simpa only [Nat.add_sub_of_le (Nat.le_of_lt hsn)] using h

/-- The exact prefactor converting the predecessor constant to the current one. -/
theorem gamma_mul_prefactor {n : ℕ} (hn : 2 ≤ n) :
    dittertConstant n * ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) = dittertConstant (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have h := gamma_succ (n := n - 1) (by omega)
  rw [Nat.sub_add_cancel hn1, Nat.cast_sub hn1, Nat.cast_one] at h
  have he : (n : ℝ) - 1 + 1 = n := by ring
  rw [he] at h
  rw [h, mul_assoc, ← mul_pow]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hmul : ((n : ℝ) - 1) / n * ((n : ℝ) / ((n : ℝ) - 1)) = 1 := by field_simp
  rw [hmul, one_pow, mul_one]

/-- The refined dimension-seven sweep parameter has the smaller path-based coefficient. -/
noncomputable def sweepParameterSeven : ℝ :=
  23 * dittertConstant 7 / (2 * (1 - dittertConstant 7))

theorem rootParameter_seven_le : rootParameter 7 ≤ 21 / 100 := by
  rw [rootParameter, Real.sqrt_le_iff]
  norm_num [dittertConstant, Nat.factorial]

theorem sweepParameter_seven_le : sweepParameterSeven ≤ 71 / 1000 := by
  norm_num [sweepParameterSeven, dittertConstant, Nat.factorial]

/-- The exact dimension-seven gap for the actual refined gamma parameters. -/
theorem spectral_gap_seven (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < (7 / 6 : ℝ) ^ 6 *
      (1 - rootParameter 7 * z - sweepParameterSeven * (1 - z ^ 2)) ^ 7 := by
  have hs : 0 ≤ 1 - z ^ 2 := by nlinarith
  have hroot := mul_le_mul_of_nonneg_right rootParameter_seven_le hz
  have hsweep := mul_le_mul_of_nonneg_right sweepParameter_seven_le hs
  have hbracket : 1 - (21 / 100 : ℝ) * z - (71 / 1000 : ℝ) * (1 - z ^ 2) ≤
      1 - rootParameter 7 * z - sweepParameterSeven * (1 - z ^ 2) := by linarith
  have hbase : 0 ≤ 1 - (21 / 100 : ℝ) * z - (71 / 1000 : ℝ) * (1 - z ^ 2) := by
    nlinarith [sq_nonneg z]
  exact (sub_pos.mp (SpectralSeven.gap_pos z hz hz1)).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hbracket 7) (by norm_num))

end DittertRybin.Certificates.SpectralParameters
