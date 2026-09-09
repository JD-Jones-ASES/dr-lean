import DR.Square.SpectralCut
import DR.Certificates.SpectralParameters
import DR.Square.Maximizers

/-!
# From the actual spectral cut to the square contradiction

The first theorem makes the analytic-to-algebraic interface explicit: actual
matrix discrepancy and an actual crossing cut imply a permanent floor. The
subsequent bounds instantiate that interface for every dimension at least eight.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralParameters

/-- A scalar certificate excludes an actual small-crossing matrix cut. -/
theorem spectral_cut_contradiction {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hsmall : a + 2 * b < 1)
    (hp : A.permanent = dittertConstant n * (1 - z ^ 2))
    (hdisc : ∀ I J : Finset (Fin n),
      |(∑ i ∈ I, rowSum A i) - I.card| + |(∑ j ∈ J, colSum A j) - J.card| ≤ a * z)
    (I J : Finset (Fin n)) (hnonempty : 0 < I.card + J.card)
    (hproper : I.card + J.card < 2 * n)
    (hcross : cutMass A I Jᶜ + cutMass A Iᶜ J ≤ 2 * b * (1 - z ^ 2))
    (hgap : 1 - z ^ 2 < ((n : ℝ) / ((n : ℝ) - 1)) ^ (n - 1) *
      (1 - a * z - b * (1 - z ^ 2)) ^ n) : False := by
  have hzsq : 0 ≤ 1 - z ^ 2 := by nlinarith
  have haz : a * z ≤ a := by nlinarith
  have hbz : 2 * b * (1 - z ^ 2) ≤ 2 * b := by nlinarith [sq_nonneg z]
  have hd0 : 0 ≤ a * z := mul_nonneg ha hz
  have hd1 : a * z < 1 := by linarith
  have hq : 0 < 1 - a * z := by linarith
  obtain ⟨B, hB, hdom⟩ := exists_doublyStochastic_dominated_of_cuts hA hq.le
    (transportCuts_of_shared_discrepancy A hA hmass (a * z) hd0 hd1 hdisc)
  have hcard := cut_card_eq_of_shared_discrepancy A hA I J (a * z)
    (2 * b * (1 - z ^ 2)) (hdisc I J) hcross (by linarith)
  have hi : 1 ≤ I.card := by omega
  have hin : I.card < n := by omega
  have hbase : 0 ≤ 1 - a * z - b * (1 - z ^ 2) := by nlinarith
  have hfloor := permanent_lower_bound_of_two_blocks A B hA hB (1 - a * z) hq hdom
    I J hcard (2 * b * (1 - z ^ 2)) hcross (by linarith)
  have heq : 1 - a * z - 2 * b * (1 - z ^ 2) / 2 = 1 - a * z - b * (1 - z ^ 2) := by ring
  rw [heq] at hfloor
  have hpred := mul_le_mul_of_nonneg_right (gamma_split_ge_predecessor hi hin)
    (pow_nonneg hbase n)
  have hper := hpred.trans hfloor
  rw [← gamma_mul_prefactor hn, hp] at hper
  have hstrict := mul_lt_mul_of_pos_left hgap (dittertConstant_pos (by omega : 0 < n))
  nlinarith

/-- The permanent deficit always has a square-root coordinate in the closed unit interval. -/
theorem dittert_contender_deficit_coordinate {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧
      dittertConstant n - A.permanent = dittertConstant n * z ^ 2 := by
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget hn A hA hmass hcont
  have hg := dittertConstant_pos (by omega : 0 < n)
  refine ⟨Real.sqrt ((dittertConstant n - A.permanent) / dittertConstant n), Real.sqrt_nonneg _, ?_, ?_⟩
  · apply Real.sqrt_le_one.mpr
    exact (div_le_one hg).mpr hdg
  · rw [Real.sq_sqrt (div_nonneg hd0 hg.le)]
    field_simp

/-- The actual marginal discrepancy is bounded by the scalar square-root parameter. -/
theorem dittert_contender_discrepancy_coordinate {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A)
    (z : ℝ) (hz : 0 ≤ z) (hdelta : dittertConstant n - A.permanent = dittertConstant n * z ^ 2)
    (I J : Finset (Fin n)) :
    |(∑ i ∈ I, rowSum A i) - I.card| + |(∑ j ∈ J, colSum A j) - J.card| ≤ rootParameter n * z := by
  have h := dittert_contender_subset_discrepancy hn A hA hmass hcont I J
  apply h.trans
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget hn A hA hmass hcont
  have hg0 := (dittertConstant_pos (by omega : 0 < n)).le
  have hg1 := dittertConstant_lt_one hn
  have hden := div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg n) hd0) (by linarith : 0 < 1 - dittertConstant n)
    (by linarith : 1 - dittertConstant n ≤ 1 - (dittertConstant n - A.permanent))
  have hroot : 0 ≤ rootParameter n * z := mul_nonneg (Real.sqrt_nonneg _) hz
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hroot, ?_⟩
  have hsquare : (rootParameter n * z) ^ 2 =
      (n : ℝ) * (dittertConstant n - A.permanent) / (1 - dittertConstant n) := by
    rw [mul_pow, rootParameter, Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hg0) (by linarith)), hdelta]
    ring
  rwa [hsquare]

/-- The raw crossing estimate in the same coordinate used by the scalar certificates. -/
theorem spectral_crossing_coordinate {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A)
    (z κ : ℝ) (hκ : 0 ≤ κ)
    (hdelta : dittertConstant n - A.permanent = dittertConstant n * z ^ 2) :
    κ * A.permanent / (1 - (dittertConstant n - A.permanent)) ≤
      (κ * dittertConstant n / (1 - dittertConstant n)) * (1 - z ^ 2) := by
  obtain ⟨_, _, _, _, hdg⟩ := dittert_contender_deficit_budget hn A hA hmass hcont
  have hg1 := dittertConstant_lt_one hn
  have hden := div_le_div_of_nonneg_left (mul_nonneg hκ (permanent_nonneg hA))
    (by linarith : 0 < 1 - dittertConstant n)
    (by linarith : 1 - dittertConstant n ≤ 1 - (dittertConstant n - A.permanent))
  have hp : A.permanent = dittertConstant n * (1 - z ^ 2) := by linarith
  calc
    _ ≤ κ * A.permanent / (1 - dittertConstant n) := hden
    _ = _ := by rw [hp]; ring

/-- Every actual global maximizer is uniform in dimensions at least eight. -/
theorem dittert_globalMax_uniform_ge_eight {n : ℕ} (hn : 8 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix n := by
  by_contra hu
  have hn2 : 2 ≤ n := by omega
  have hnR : (8 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨z, hz, hz1, hdelta⟩ := dittert_contender_deficit_coordinate hn2 A hA hmass hcont
  obtain ⟨I, J, hnonempty, hproper, _, hcross⟩ := dittert_globalMax_cut hn2 A hA hmass hmax hu
  have ha : 0 ≤ rootParameter n := Real.sqrt_nonneg _
  have hb : 0 ≤ sweepParameter n := by
    unfold sweepParameter
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (dittertConstant_pos (by omega : 0 < n)).le) (by have := dittertConstant_lt_one hn2; linarith)
  have hsmall : rootParameter n + 2 * sweepParameter n < 1 := by
    have har := (le_div_iff₀ (show (0 : ℝ) < n by linarith)).mp (rootParameter_le_scaled_cap hn)
    have hbr := (le_div_iff₀ (show (0 : ℝ) < n by linarith)).mp (sweepParameter_le_scaled_cap hn)
    nlinarith
  apply spectral_cut_contradiction hn2 A hA hmass (rootParameter n) (sweepParameter n) z
    ha hb hz hz1 hsmall (by linarith) (dittert_contender_discrepancy_coordinate hn2 A hA hmass hcont z hz hdelta)
    I J hnonempty hproper _ (spectral_gap_pos hn z hz hz1)
  have hbound := spectral_crossing_coordinate hn2 A hA hmass hcont z
    ((n : ℝ) * (2 * n - 1) / 2)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (by norm_num)) hdelta
  have hleft : (n : ℝ) * (2 * n - 1) / 2 * A.permanent /
      (1 - (dittertConstant n - A.permanent)) =
      n * (2 * n - 1) * A.permanent / (2 * (1 - (dittertConstant n - A.permanent))) := by
    simp only [div_mul_eq_div_div]; ring
  have hright : ((n : ℝ) * (2 * n - 1) / 2 * dittertConstant n / (1 - dittertConstant n)) *
      (1 - z ^ 2) = 2 * sweepParameter n * (1 - z ^ 2) := by
    simp only [sweepParameter, div_mul_eq_div_div]; ring
  rw [hleft, hright] at hbound
  exact hcross.trans hbound

/-- The full closed-simplex inequality and unique equality in every dimension at least eight. -/
theorem dittert_ge_eight {n : ℕ} (hn : 8 ≤ n) : DittertMaximizer n :=
  dittertMaximizer_of_globalMax_uniform (by omega) (dittert_globalMax_uniform_ge_eight hn)

end DittertRybin
