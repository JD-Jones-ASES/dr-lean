import DR.Rectangular.FourRowContenderInitial

/-!
# The scalar centered-cubic concentration bootstrap

This module isolates the exact analytic consequence of the leading gauge and
collision-remainder estimates. Its hypotheses are those independent estimates,
not the desired concentration bounds. The actual contender supplies the exact
uniform upper comparison in `FourRowContenderInitial`.
-/

namespace DittertRybin

open scoped BigOperators

noncomputable def fourRowGaugeVariance {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j, (a j - (∑ k, a k) / n) ^ 2

/-- The cubic remainder about the mean is exact for arbitrary real coordinates. -/
theorem fourRow_centered_cubic {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ j, (6 * a j ^ 2 - 17 * a j ^ 3)) =
      6 * (∑ j, a j) ^ 2 / n - 17 * (∑ j, a j) ^ 3 / (n : ℝ) ^ 2 +
        ∑ j, (a j - (∑ k, a k) / n) ^ 2 * (6 - 17 * (a j + 2 * (∑ k, a k) / n)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let H := ∑ j, a j
  let h := H / n
  have hc : (∑ j, (a j - h)) = 0 := by
    simp [Finset.sum_sub_distrib, h, H]
    field_simp
    ring
  have ht (j : Fin n) : 6 * a j ^ 2 - 17 * a j ^ 3 =
      6 * h ^ 2 - 17 * h ^ 3 + (12 * h - 51 * h ^ 2) * (a j - h) +
        (a j - h) ^ 2 * (6 - 17 * (a j + 2 * h)) := by ring
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum, hc]
  simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  dsimp [h, H]
  congr 1
  · field_simp
  · congr 1
    funext j
    ring

/-- A small initial coordinate cap makes the exact cubic uniformly convex on its range. -/
theorem fourRow_centered_cubic_lower {n : ℕ} (hn : 500 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ j, a j ≤ 21 / 100) (hH : (∑ j, a j) ≤ 1) :
    6 * (∑ j, a j) ^ 2 / n - 17 * (∑ j, a j) ^ 3 / (n : ℝ) ^ 2 +
      2 * fourRowGaugeVariance a ≤ ∑ j, (6 * a j ^ 2 - 17 * a j ^ 3) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  have hmean : (∑ j, a j) / n ≤ 1 / 500 := by
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hcoef (j : Fin n) : 2 ≤ 6 - 17 * (a j + 2 * (∑ k, a k) / n) := by
    rw [mul_div_assoc]
    linarith [ha j]
  rw [fourRow_centered_cubic (by omega)]
  gcongr
  unfold fourRowGaugeVariance
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcoef j)
    (sq_nonneg (a j - (∑ k, a k) / n))

/-- Exact variance consequences of the independent gauge and failure estimates.
Here `ρ` denotes the row variance, not its square root. The scaled output
avoids any ambiguity in powers of the dimension. -/
theorem fourRow_gauge_variance_bounds {n : ℕ} (hn : 500 ≤ n) (a : Fin n → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha : ∀ j, a j ≤ 21 / 100)
    (hH : (∑ j, a j) ≤ 1) (ρ Q : ℝ) (hρ : 0 ≤ ρ)
    (hgap : 29 / 32 + (61 / 512) * ρ ≤ (∑ j, a j) ^ 2)
    (hlower : (∑ j, (6 * a j ^ 2 - 17 * a j ^ 3)) ≤ Q)
    (hupper : Q ≤ (29 / 32 : ℝ) *
      (6 / n - 11 / (n : ℝ) ^ 2 + 6 / (n : ℝ) ^ 3)) :
    fourRowGaugeVariance a * (n : ℝ) ^ 2 < 4 ∧ ρ * n < 10 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  have hH0 : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha0 j
  have hH3 : (∑ j, a j) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hH0 hH 3
  have hV : 0 ≤ fourRowGaugeVariance a := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbase := (fourRow_centered_cubic_lower hn a ha hH).trans hlower
  have hcube : (∑ j, a j) ^ 3 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hH3 (sq_nonneg _)
  have hlo : 6 * (∑ j, a j) ^ 2 / n - 17 / (n : ℝ) ^ 2 +
      2 * fourRowGaugeVariance a ≤ Q := by
    simp only [div_eq_mul_inv] at hbase hcube ⊢
    nlinarith only [hbase, hcube]
  have hlo' := mul_le_mul_of_nonneg_right hlo (sq_nonneg (n : ℝ))
  have hup' := mul_le_mul_of_nonneg_right hupper (sq_nonneg (n : ℝ))
  have hscaledlo : 6 * (∑ j, a j) ^ 2 * n - 17 +
      2 * fourRowGaugeVariance a * (n : ℝ) ^ 2 ≤ Q * (n : ℝ) ^ 2 := by
    calc
      _ = (6 * (∑ j, a j) ^ 2 / n - 17 / (n : ℝ) ^ 2 +
        2 * fourRowGaugeVariance a) * (n : ℝ) ^ 2 := by field_simp
      _ ≤ _ := hlo'
  have hscaledup : Q * (n : ℝ) ^ 2 ≤
      (29 / 32) * (6 * n - 11 + 6 / (n : ℝ)) := by
    calc
      _ ≤ (29 / 32 : ℝ) * (6 / n - 11 / (n : ℝ) ^ 2 +
        6 / (n : ℝ) ^ 3) * (n : ℝ) ^ 2 := hup'
      _ = _ := by field_simp
  have hinv : 1 / (n : ℝ) ≤ 1 / 500 := by
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hHlow : 29 / 32 ≤ (∑ j, a j) ^ 2 := by linarith
  have hgapscaled := mul_le_mul_of_nonneg_right hgap hnpos.le
  have hHscaled := mul_le_mul_of_nonneg_right hHlow hnpos.le
  have hVscaled : 0 ≤ fourRowGaugeVariance a * (n : ℝ) ^ 2 :=
    mul_nonneg hV (sq_nonneg _)
  simp only [div_eq_mul_inv] at hinv hscaledup
  constructor <;> nlinarith only [hinv, hscaledlo, hscaledup, hgapscaled, hHscaled, hVscaled]

/-- The exact second-moment decomposition for the gauge coordinates. -/
theorem fourRowGaugeVariance_identity {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ j, a j ^ 2) * (n : ℝ) ^ 2 = (∑ j, a j) ^ 2 * n +
      fourRowGaugeVariance a * (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [fourRowGaugeVariance, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The gauge variance gives both sharp-enough actual column concentration estimates. -/
theorem fourRow_gauge_column_bounds {n : ℕ} (hn : 500 ≤ n) (a c : Fin n → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (hH : (∑ j, a j) ≤ 1)
    (hV : fourRowGaugeVariance a * (n : ℝ) ^ 2 < 4)
    (hc : ∀ j, c j ^ 2 ≤ (4 / 3) * a j ^ 2) :
    (∀ j, c j < 7 / (2 * (n : ℝ))) ∧ (∑ j, c j ^ 2) < 7 / (5 * (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  have hH0 : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha0 j
  have hH2 : (∑ j, a j) ^ 2 ≤ 1 := by nlinarith
  have hmoment := fourRowGaugeVariance_identity (by omega) a
  have hHscaled := mul_le_mul_of_nonneg_right hH2 hnpos.le
  have hmomentcap : (∑ j, a j ^ 2) * (n : ℝ) ^ 2 < n + 4 := by linarith
  constructor
  · intro j
    have hpart : (a j - (∑ k, a k) / n) ^ 2 ≤ fourRowGaugeVariance a := by
      unfold fourRowGaugeVariance
      exact Finset.single_le_sum (fun k _ => sq_nonneg (a k - (∑ l, a l) / n))
        (Finset.mem_univ j)
    have hpartscaled := mul_le_mul_of_nonneg_right hpart (sq_nonneg (n : ℝ))
    have hid : ((n : ℝ) * a j - ∑ k, a k) ^ 2 =
        (a j - (∑ k, a k) / n) ^ 2 * (n : ℝ) ^ 2 := by field_simp
    rw [← hid] at hpartscaled
    have haj : (n : ℝ) * a j < 3 := by nlinarith
    have haj0 : 0 ≤ (n : ℝ) * a j := mul_nonneg hnpos.le (ha0 j)
    have hcscaled := mul_le_mul_of_nonneg_right (hc j) (sq_nonneg (n : ℝ))
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  · have hcsum : (∑ j, c j ^ 2) ≤ (4 / 3) * ∑ j, a j ^ 2 := by
      simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun j _ => hc j)
    have hcscaled := mul_le_mul_of_nonneg_right hcsum (sq_nonneg (n : ℝ))
    have hscaled : (∑ j, c j ^ 2) * (n : ℝ) ^ 2 < (7 / 5) * n := by nlinarith
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith

end DittertRybin
