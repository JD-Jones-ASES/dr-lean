import DR.Square.MarginalDiscrepancy
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Sharper marginal and cut bounds in dimension six

Section 2 of the Analytic-Lab P0174 order-six proof uses the local Bernoulli
variance, rather than its global bound `1/4`. The variance estimate below is
proved throughout the interval between the two entropy arguments. All subset
bounds refer to the actual positive marginals and their actual product deficit.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

noncomputable section

private theorem binary_entropy_local_corrected_hasDerivAt (p B : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun q => 2 * B * binaryRelativeEntropy p q - (q - p) ^ 2)
      (2 * (q - p) * (B / (q * (1 - q)) - 1)) q := by
  convert ((binaryRelativeEntropy_hasDerivAt p hq hq1).const_mul (2 * B)).sub
    (((hasDerivAt_id q).sub_const p).pow 2) using 1 <;> try rfl
  simp only [id_eq]
  ring

/-- Integrating the entropy derivative requires only a variance bound on the
closed interval joining `p` and `q`. The proof uses derivative monotonicity. -/
theorem binaryRelativeEntropy_local_variance {p q B : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hB : ∀ z ∈ uIcc p q, z * (1 - z) ≤ B) :
    (q - p) ^ 2 ≤ 2 * B * binaryRelativeEntropy p q := by
  let f : ℝ → ℝ := fun z => 2 * B * binaryRelativeEntropy p z - (z - p) ^ 2
  have hf (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :=
    binary_entropy_local_corrected_hasDerivAt p B hz hz1
  have hratio (z : ℝ) (hz : 0 < z) (hz1 : z < 1) (hzB : z * (1 - z) ≤ B) :
      0 ≤ B / (z * (1 - z)) - 1 := by
    have hv : 0 < z * (1 - z) := mul_pos hz (by linarith)
    have h := (le_div_iff₀ hv).mpr (by simpa using hzB : 1 * (z * (1 - z)) ≤ B)
    linarith
  have hpzero : f p = 0 := by simp [f, binaryRelativeEntropy_self]
  rcases le_total p q with hpq | hqp
  · rw [uIcc_of_le hpq] at hB
    have hm : MonotoneOn f (Icc p q) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
      · intro z hz
        exact (hf z (lt_of_lt_of_le hp hz.1) (lt_of_le_of_lt hz.2 hq1)).continuousAt.continuousWithinAt
      · intro z hz
        exact (hf z (lt_of_lt_of_le hp (interior_subset hz).1)
          (lt_of_le_of_lt (interior_subset hz).2 hq1)).hasDerivWithinAt
      · intro z hz
        exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (interior_subset hz).1))
          (hratio z (lt_of_lt_of_le hp (interior_subset hz).1)
            (lt_of_le_of_lt (interior_subset hz).2 hq1) (hB z (interior_subset hz)))
    have h := hm ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
    rw [hpzero] at h
    dsimp [f] at h
    linarith
  · rw [uIcc_of_ge hqp] at hB
    have hm : AntitoneOn f (Icc q p) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q p)
      · intro z hz
        exact (hf z (lt_of_lt_of_le hq hz.1) (lt_of_le_of_lt hz.2 hp1)).continuousAt.continuousWithinAt
      · intro z hz
        exact (hf z (lt_of_lt_of_le hq (interior_subset hz).1)
          (lt_of_le_of_lt (interior_subset hz).2 hp1)).hasDerivWithinAt
      · intro z hz
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr (interior_subset hz).2))
          (hratio z (lt_of_lt_of_le hq (interior_subset hz).1)
            (lt_of_le_of_lt (interior_subset hz).2 hp1) (hB z (interior_subset hz)))
    have h := hm ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
    rw [hpzero] at h
    dsimp [f] at h
    linarith

/-- The local Bernoulli-variance envelope drops the nonpositive quadratic term. -/
theorem binary_variance_le_local_envelope (p z eta : ℝ) (hz : |z - p| ≤ eta) :
    z * (1 - z) ≤ p * (1 - p) + |1 - 2 * p| * eta := by
  have h := mul_le_mul_of_nonneg_left hz (abs_nonneg (1 - 2 * p))
  have hm := le_abs_self ((1 - 2 * p) * (z - p))
  rw [abs_mul] at hm
  nlinarith [sq_nonneg (z - p)]

/-- Grouping the actual marginal product into a subset and its complement. -/
theorem subset_binaryRelativeEntropy_le_neg_log {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIc : Iᶜ.Nonempty) :
    n * binaryRelativeEntropy (I.card / n) ((∑ i ∈ I, r i) / n) ≤
      -Real.log (∏ i, r i) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hk : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI.card_pos
  have hkc : (0 : ℝ) < Iᶜ.card := Nat.cast_pos.mpr hIc.card_pos
  have hcard : (Iᶜ.card : ℝ) = n - I.card := by
    rw [Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_univ I : I.card ≤ n)]
  have hRI : 0 < ∑ i ∈ I, r i := sum_pos (fun i _ => hr i) hI
  have hRc : 0 < ∑ i ∈ Iᶜ, r i := sum_pos (fun i _ => hr i) hIc
  have hsumc : (∑ i ∈ Iᶜ, r i) = n - ∑ i ∈ I, r i := by
    have h := Finset.sum_add_sum_compl I r
    rw [hsum] at h
    linarith
  have hgm := add_le_add
    (sum_log_le_card_mul_log_mean I r hI (fun i _ => hr i))
    (sum_log_le_card_mul_log_mean Iᶜ r hIc (fun i _ => hr i))
  rw [Finset.sum_add_sum_compl, hcard, hsumc,
    ← Real.log_prod (fun i _ => (hr i).ne')] at hgm
  have hscaled := binaryRelativeEntropy_scaled hnR hk (by linarith) hRI (by linarith)
  linarith

/-- The physical order-six parameter. -/
def sixDeficitParameter (delta : ℝ) : ℝ := Real.sqrt (6 * delta / (1 - delta))

/-- The seven-entry entropy-cut coefficient table, extended by zero. -/
def sixCutCoefficient (k : ℕ) (t : ℝ) : ℝ :=
  match k with
  | 1 | 5 => 5 / 3 + (71 / 75) * t
  | 2 | 4 => 8 / 3 + (71 / 150) * t
  | 3 => 3
  | _ => 0

/-- The worst cut-cardinality coefficient ratio. -/
def sixCutStar (t : ℝ) : ℝ := 17 / 3 + (71 / 150) * t

/-- The rational common domination and unbalanced-cut factor. -/
def sixDominationFactor (t : ℝ) : ℝ := 1 - (243 / 250) * t - (41 / 1000) * t ^ 2

/-- The complete seven-entry table is obtained from the local variance envelope. -/
theorem sixCutCoefficient_eq (k : Fin 7) (hk : 0 < k.val) (hk6 : k.val < 6) (t : ℝ) :
    sixCutCoefficient k t =
      12 * (((k : ℝ) / 6) * (1 - (k : ℝ) / 6) +
        |1 - 2 * ((k : ℝ) / 6)| * ((71 / 600) * t)) := by
  fin_cases k <;> norm_num [sixCutCoefficient] at * <;> ring


theorem sixCutCoefficient_nonneg (k : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ sixCutCoefficient k t := by
  fin_cases k <;> norm_num [sixCutCoefficient] <;> linarith

theorem sixCutCoefficient_le_three (k : Fin 7) {t : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    sixCutCoefficient k t ≤ 3 := by
  fin_cases k <;> norm_num [sixCutCoefficient] <;> linarith

/-- All twenty-one ordered positive capacity-cut cardinalities. -/
theorem sixCutCoefficient_capacity_ratio (k l : Fin 7) (hkl : 6 < k.val + l.val)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    (sixCutCoefficient k t + sixCutCoefficient l t) / ((k : ℝ) + l - 6) ^ 2 ≤ sixCutStar t := by
  fin_cases k <;> fin_cases l <;>
    norm_num [sixCutCoefficient, sixCutStar] at * <;> linarith

/-- All forty-two ordered unequal cut cardinalities, including zero and six. -/
theorem sixCutCoefficient_unbalanced_ratio (k l : Fin 7) (hkl : k ≠ l)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    (sixCutCoefficient k t + sixCutCoefficient l t) / ((k : ℝ) - l) ^ 2 ≤ sixCutStar t := by
  fin_cases k <;> fin_cases l <;>
    norm_num [sixCutCoefficient, sixCutStar] at * <;> linarith

theorem sixDeficitParameter_sq {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    sixDeficitParameter delta ^ 2 = 6 * delta / (1 - delta) := by
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

theorem sixDeficitParameter_nonneg (delta : ℝ) : 0 ≤ sixDeficitParameter delta :=
  Real.sqrt_nonneg _

theorem sixDeficitParameter_le_cap {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 6) : sixDeficitParameter delta < 31 / 100 := by
  have hg : dittertConstant 6 = 5 / 324 := by norm_num [dittertConstant, Nat.factorial]
  have hden : 0 < 1 - delta := by rw [hg] at hdg; linarith
  have hfrac : 6 * delta / (1 - delta) ≤ 30 / 319 := by
    apply (div_le_iff₀ hden).mpr
    rw [hg] at hdg
    linarith
  have hsq := sixDeficitParameter_sq hd0 (by linarith)
  have ht := sixDeficitParameter_nonneg delta
  nlinarith

/-- The preliminary Pinsker estimate gives the certified entropy interval. -/
theorem six_subset_coarse_discrepancy (r : Fin 6 → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 6) {rho delta : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd1 : delta < 1)
    (I : Finset (Fin 6)) :
    |(∑ i ∈ I, r i) - I.card| ≤ (71 / 100) * sixDeficitParameter delta := by
  have hs := subset_discrepancy_sq_le (by norm_num) r hr hsum hprod hrho hrd hd1 I
  have hden : 0 < 2 * (1 - delta) := by linarith
  have hm : (6 : ℝ) * rho / (2 * (1 - delta)) ≤ 6 * delta / (2 * (1 - delta)) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have ht := sixDeficitParameter_nonneg delta
  have htsq := sixDeficitParameter_sq (by linarith) hd1
  have heq : 6 * delta / (2 * (1 - delta)) = (6 * delta / (1 - delta)) / 2 := by
    have : 1 - delta ≠ 0 := by linarith
    field_simp
  rw [heq, ← htsq] at hm
  have habs := sq_abs ((∑ i ∈ I, r i) - I.card)
  nlinarith [hs.trans hm, abs_nonneg ((∑ i ∈ I, r i) - I.card)]

/-- The actual sharper subset bound, with the complete seven-entry table. -/
theorem six_subset_discrepancy_sq_le (r : Fin 6 → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 6) {rho delta : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd1 : delta < 1)
    (I : Finset (Fin 6)) :
    ((∑ i ∈ I, r i) - I.card) ^ 2 ≤
      sixCutCoefficient I.card (sixDeficitParameter delta) * rho / (1 - delta) := by
  have hcardle : I.card ≤ 6 := by simpa using Finset.card_le_univ I
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp [sixCutCoefficient]
  rcases Iᶜ.eq_empty_or_nonempty with hfull | hIc
  · have hIu : I = Finset.univ := by
      simpa using congrArg (fun s : Finset (Fin 6) => sᶜ) hfull
    simp [hIu, hsum, sixCutCoefficient]
  have hk0 : 0 < I.card := hI.card_pos
  have hkc : 0 < Iᶜ.card := hIc.card_pos
  have hk6 : I.card < 6 := by simpa [Finset.card_compl] using hkc
  have hkR : (0 : ℝ) < I.card := Nat.cast_pos.mpr hk0
  have hkR6 : (I.card : ℝ) < 6 := Nat.cast_lt.mpr hk6
  have hRI : 0 < ∑ i ∈ I, r i := sum_pos (fun i _ => hr i) hI
  have hRc : 0 < ∑ i ∈ Iᶜ, r i := sum_pos (fun i _ => hr i) hIc
  have hsumc := Finset.sum_add_sum_compl I r
  rw [hsum] at hsumc
  have hRN : (∑ i ∈ I, r i) < 6 := by linarith
  let k : Fin 7 := ⟨I.card, by omega⟩
  let t := sixDeficitParameter delta
  let B := ((I.card : ℝ) / 6) * (1 - (I.card : ℝ) / 6) +
    |1 - 2 * ((I.card : ℝ) / 6)| * ((71 / 600) * t)
  have ht : 0 ≤ t := sixDeficitParameter_nonneg delta
  have hbase : 0 ≤ 1 - (I.card : ℝ) / 6 := by linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCeq : sixCutCoefficient I.card t = 12 * B := by
    exact sixCutCoefficient_eq k hk0 hk6 t
  have hdist : |(∑ i ∈ I, r i) / 6 - I.card / 6| ≤ (71 / 600) * t := by
    have h := six_subset_coarse_discrepancy r hr hsum hprod hrho hrd hd1 I
    rw [← sub_div, abs_div]
    norm_num
    dsimp [t]
    linarith
  have hvar (z : ℝ) (hz : z ∈ uIcc ((I.card : ℝ) / 6) ((∑ i ∈ I, r i) / 6)) :
      z * (1 - z) ≤ B := by
    exact binary_variance_le_local_envelope _ _ _ ((abs_sub_left_of_mem_uIcc hz).trans hdist)
  have hb := binaryRelativeEntropy_local_variance
    (by positivity : 0 < (I.card : ℝ) / 6) (by linarith : (I.card : ℝ) / 6 < 1)
    (by positivity : 0 < (∑ i ∈ I, r i) / 6) (by linarith : (∑ i ∈ I, r i) / 6 < 1) hvar
  have he := subset_binaryRelativeEntropy_le_neg_log (by norm_num) r hr hsum I hI hIc
  rw [hprod] at he
  have hl := he.trans (neg_log_one_sub_le hrho hrd hd1)
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 12 * B)
  have hid : ((∑ i ∈ I, r i) - I.card) ^ 2 =
      36 * ((∑ i ∈ I, r i) / 6 - I.card / 6) ^ 2 := by ring
  rw [hid, hCeq]
  norm_num only [Nat.cast_ofNat] at hm
  rw [← mul_div_assoc] at hm
  nlinarith


/-- A two-term weighted Cauchy inequality stated directly through squared bounds. -/
theorem add_sq_le_of_sq_le_mul {x y a b u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : x ^ 2 ≤ a * u) (hy : y ^ 2 ≤ b * v) :
    (x + y) ^ 2 ≤ (a + b) * (u + v) := by
  have hmul := mul_le_mul hx hy (sq_nonneg y) (mul_nonneg ha hu)
  have hcross : (x * y) ^ 2 ≤ (a * v) * (b * u) := by nlinarith [hmul]
  have h := two_mul_le_add_of_sq_le_mul (mul_nonneg ha hv) (mul_nonneg hb hu) hcross
  nlinarith

/-- The sharper row and column constants share one product-deficit budget. -/
theorem six_shared_subset_discrepancy_sq_le (r c : Fin 6 → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = 6) (hsumc : ∑ j, c j = 6)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd1 : delta < 1) (I J : Finset (Fin 6)) :
    (|(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card|) ^ 2 ≤
      (sixCutCoefficient I.card (sixDeficitParameter delta) +
        sixCutCoefficient J.card (sixDeficitParameter delta)) * delta / (1 - delta) := by
  have hI : I.card < 7 := by have := Finset.card_le_univ I; simp at this; omega
  have hJ : J.card < 7 := by have := Finset.card_le_univ J; simp at this; omega
  have ht := sixDeficitParameter_nonneg delta
  have hci := sixCutCoefficient_nonneg ⟨I.card, hI⟩ ht
  have hcj := sixCutCoefficient_nonneg ⟨J.card, hJ⟩ ht
  have hrb := six_subset_discrepancy_sq_le r hr hsumr hprodr hrho (by linarith) hd1 I
  have hcb := six_subset_discrepancy_sq_le c hc hsumc hprodc hsigma (by linarith) hd1 J
  rw [mul_div_assoc] at hrb hcb
  rw [← sq_abs ((∑ i ∈ I, r i) - I.card)] at hrb
  rw [← sq_abs ((∑ j ∈ J, c j) - J.card)] at hcb
  have hden : 0 < 1 - delta := by linarith
  have h := add_sq_le_of_sq_le_mul hci hcj (div_nonneg hrho hden.le)
    (div_nonneg hsigma hden.le) hrb hcb
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hbudget hden.le) (add_nonneg hci hcj)
  rw [add_div] at hb
  simpa only [mul_div_assoc] using h.trans hb

/-- The order-six shared square-root bound with its exact cut coefficients. -/
theorem six_shared_subset_discrepancy_le (r c : Fin 6 → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = 6) (hsumc : ∑ j, c j = 6)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd1 : delta < 1) (I J : Finset (Fin 6)) :
    |(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card| ≤
      Real.sqrt ((sixCutCoefficient I.card (sixDeficitParameter delta) +
        sixCutCoefficient J.card (sixDeficitParameter delta)) * delta / (1 - delta)) :=
  Real.le_sqrt_of_sq_le (six_shared_subset_discrepancy_sq_le r c hr hc hsumr hsumc
    hprodr hprodc hrho hsigma hbudget hd1 I J)

/-- The rational envelope has a strictly positive squared slack even at zero. -/
theorem six_entropy_envelope_sq {t : ℝ} (ht : 0 ≤ t) :
    17 / 18 + (71 / 900) * t < ((243 / 250 : ℝ) + (41 / 1000) * t) ^ 2 := by
  nlinarith [sq_nonneg t]

theorem six_entropy_envelope {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (17 / 18 + (71 / 900) * t) ≤ (243 / 250) + (41 / 1000) * t := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, (six_entropy_envelope_sq ht).le⟩

theorem sixDominationFactor_gt_two_thirds {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    2 / 3 < sixDominationFactor t := by
  unfold sixDominationFactor
  nlinarith [sq_nonneg (31 / 100 - t)]

theorem sixDominationFactor_le_one {t : ℝ} (ht : 0 ≤ t) : sixDominationFactor t ≤ 1 := by
  unfold sixDominationFactor
  nlinarith [sq_nonneg t]

/-- The common rational envelope turns any certified coefficient ratio into a
linear discrepancy allowance. -/
theorem six_discrepancy_le_envelope {x C a delta : ℝ}
    (hd0 : 0 ≤ delta) (hd1 : delta < 1) (ha : 0 ≤ a)
    (hx : x ^ 2 ≤ C * delta / (1 - delta))
    (hC : C ≤ sixCutStar (sixDeficitParameter delta) * a ^ 2) :
    x ≤ a * (1 - sixDominationFactor (sixDeficitParameter delta)) := by
  let t := sixDeficitParameter delta
  have ht : 0 ≤ t := sixDeficitParameter_nonneg delta
  have hden : 0 < 1 - delta := by linarith
  have htsq : t ^ 2 = 6 * delta / (1 - delta) := sixDeficitParameter_sq hd0 hd1
  have henv : sixCutStar t / 6 ≤ ((243 / 250 : ℝ) + (41 / 1000) * t) ^ 2 := by
    have hnorm : sixCutStar t / 6 = 17 / 18 + (71 / 900) * t := by unfold sixCutStar; ring
    rw [hnorm]
    exact (six_entropy_envelope_sq ht).le
  have hmul := mul_le_mul_of_nonneg_right hC (div_nonneg hd0 hden.le)
  have heq : sixCutStar t * a ^ 2 * (delta / (1 - delta)) =
      (sixCutStar t / 6) * (a * t) ^ 2 := by rw [mul_pow, htsq]; ring
  have hb : x ^ 2 ≤ (sixCutStar t / 6) * (a * t) ^ 2 := by
    change C * (delta / (1 - delta)) ≤ sixCutStar t * a ^ 2 * (delta / (1 - delta)) at hmul
    rw [heq] at hmul
    rw [mul_div_assoc] at hx
    exact hx.trans hmul
  have hm := mul_le_mul_of_nonneg_right henv (sq_nonneg (a * t))
  have hrhs : 0 ≤ a * (1 - sixDominationFactor t) :=
    mul_nonneg ha (sub_nonneg.mpr (sixDominationFactor_le_one ht))
  apply nonneg_le_nonneg_of_sq_le_sq hrhs
  simp only [← sq]
  calc
    x ^ 2 ≤ (sixCutStar t / 6) * (a * t) ^ 2 := hb
    _ ≤ ((243 / 250 : ℝ) + (41 / 1000) * t) ^ 2 * (a * t) ^ 2 := hm
    _ = (a * (1 - sixDominationFactor t)) ^ 2 := by unfold sixDominationFactor; ring


/-- Positive capacity cuts receive a discrepancy allowance proportional to the
integer excess cardinality, using the same rational factor `q`. -/
theorem six_shared_capacity_discrepancy (r c : Fin 6 → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = 6) (hsumc : ∑ j, c j = 6)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd1 : delta < 1)
    (ht1 : sixDeficitParameter delta ≤ 31 / 100)
    (I J : Finset (Fin 6)) (hIJ : 6 < I.card + J.card) :
    |(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card| ≤
      ((I.card : ℝ) + J.card - 6) * (1 - sixDominationFactor (sixDeficitParameter delta)) := by
  let k : Fin 7 := ⟨I.card, by have := Finset.card_le_univ I; simp at this; omega⟩
  let l : Fin 7 := ⟨J.card, by have := Finset.card_le_univ J; simp at this; omega⟩
  have ha : 0 < (I.card : ℝ) + J.card - 6 := by
    have : (6 : ℝ) < I.card + J.card := by exact_mod_cast hIJ
    linarith
  have hratio := sixCutCoefficient_capacity_ratio k l hIJ (sixDeficitParameter_nonneg delta) ht1
  have hC := (div_le_iff₀ (sq_pos_of_pos ha)).mp hratio
  exact six_discrepancy_le_envelope (by linarith) hd1 ha.le
    (six_shared_subset_discrepancy_sq_le r c hr hc hsumr hsumc hprodr hprodc
      hrho hsigma hbudget hd1 I J) hC

/-- Unequal cut cardinalities receive the corresponding absolute difference
allowance, again with the same rational factor `q`. -/
theorem six_shared_unbalanced_discrepancy (r c : Fin 6 → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = 6) (hsumc : ∑ j, c j = 6)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd1 : delta < 1)
    (ht1 : sixDeficitParameter delta ≤ 31 / 100)
    (I J : Finset (Fin 6)) (hIJ : I.card ≠ J.card) :
    |(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card| ≤
      |(I.card : ℝ) - J.card| * (1 - sixDominationFactor (sixDeficitParameter delta)) := by
  let k : Fin 7 := ⟨I.card, by have := Finset.card_le_univ I; simp at this; omega⟩
  let l : Fin 7 := ⟨J.card, by have := Finset.card_le_univ J; simp at this; omega⟩
  have hkl : k ≠ l := by intro h; exact hIJ (congrArg Fin.val h)
  have ha : (I.card : ℝ) - J.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hIJ)
  have hratio := sixCutCoefficient_unbalanced_ratio k l hkl (sixDeficitParameter_nonneg delta) ht1
  have hC := (div_le_iff₀ (sq_pos_of_ne_zero ha)).mp hratio
  rw [← sq_abs ((I.card : ℝ) - J.card)] at hC
  exact six_discrepancy_le_envelope (by linarith) hd1 (abs_nonneg _)
    (six_shared_subset_discrepancy_sq_le r c hr hc hsumr hsumc hprodr hprodc
      hrho hsigma hbudget hd1 I J) hC

/-- The rational marginal cap for the actual dimension-six parameter. -/
theorem six_marginal_cap (r : Fin 6 → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 6) {rho delta : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd1 : delta < 1) (i : Fin 6) :
    r i ≤ 1 + (71 / 100) * sixDeficitParameter delta := by
  have h := six_subset_coarse_discrepancy r hr hsum hprod hrho hrd hd1 {i}
  simp only [sum_singleton, Finset.card_singleton, Nat.cast_one] at h
  linarith [le_abs_self (r i - 1)]

/-- The six-dimensional actual contender satisfies the rational marginal cap;
zero matrix entries need no separate assumption or case. -/
theorem six_contender_marginal_cap (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A) :
    (∀ i, rowSum A i ≤ 1 + (71 / 100) * sixDeficitParameter (dittertConstant 6 - A.permanent)) ∧
    (∀ j, colSum A j ≤ 1 + (71 / 100) * sixDeficitParameter (dittertConstant 6 - A.permanent)) := by
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, _, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  constructor
  · exact six_marginal_cap (rowSum A) hr hmass (by ring) hrho (by linarith) hd1
  · exact six_marginal_cap (colSum A) hc (by rwa [← totalMass_eq_sum_colSum])
      (by ring) hsigma (by linarith) hd1

end
end DittertRybin
