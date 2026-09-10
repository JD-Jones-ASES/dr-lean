import DR.Entropy
import DR.Square.Contenders
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Product deficits control every marginal subset

We prove the binary relative entropy inequality by differentiating in its
second argument. Grouped AM–GM is proved in logarithmic form by summing the
scalar tangent inequality for `log`. Together these give the sharp factor two
in the discrepancy estimate, including empty and full subsets. No positivity
of individual matrix cells is used: only the positive marginals are needed.

The shared row and column deficit budget controls the sum of both discrepancies.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

noncomputable section

/-- Binary relative entropy, on the open probability interval. -/
def binaryRelativeEntropy (p q : ℝ) : ℝ :=
  p * (Real.log p - Real.log q) +
    (1 - p) * (Real.log (1 - p) - Real.log (1 - q))

theorem binaryRelativeEntropy_self (p : ℝ) : binaryRelativeEntropy p p = 0 := by
  simp [binaryRelativeEntropy]

theorem binaryRelativeEntropy_hasDerivAt (p : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (binaryRelativeEntropy p) ((q - p) / (q * (1 - q))) q := by
  have hq0 := hq.ne'
  have h1q0 : 1 - q ≠ 0 := by linarith
  have hd := (((hasDerivAt_const q (Real.log p)).sub
    (Real.hasDerivAt_log hq0)).const_mul p).add
    (((hasDerivAt_const q (Real.log (1 - p))).sub
      (((hasDerivAt_id q).const_sub 1).log h1q0)).const_mul (1 - p))
  convert hd using 1 <;> try rfl
  simp only [id_eq]
  field_simp
  ring

private theorem binary_entropy_corrected_hasDerivAt (p : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun q => binaryRelativeEntropy p q - 2 * (q - p) ^ 2)
      ((q - p) * (1 / (q * (1 - q)) - 4)) q := by
  convert (binaryRelativeEntropy_hasDerivAt p hq hq1).sub
    ((((hasDerivAt_id q).sub_const p).pow 2).const_mul 2) using 1 <;> try rfl
  simp only [id_eq]
  ring

private theorem inverse_binary_variance_ge_four {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ 1 / (q * (1 - q)) - 4 := by
  have hd : 0 < q * (1 - q) := mul_pos hq (by linarith)
  have h : 4 * (q * (1 - q)) ≤ 1 := by nlinarith [sq_nonneg (2 * q - 1)]
  have hi : 4 ≤ 1 / (q * (1 - q)) := (le_div_iff₀ hd).mpr h
  linarith

/-- The binary Pinsker estimate, proved by the sign of an explicit derivative. -/
theorem binaryRelativeEntropy_ge_two_sq {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (q - p) ^ 2 ≤ binaryRelativeEntropy p q := by
  let f : ℝ → ℝ := fun t => binaryRelativeEntropy p t - 2 * (t - p) ^ 2
  have hf (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :=
    binary_entropy_corrected_hasDerivAt p ht ht1
  have hpzero : f p = 0 := by simp [f, binaryRelativeEntropy_self]
  rcases le_total p q with hpq | hqp
  · have hm : MonotoneOn f (Icc p q) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
      · intro t ht
        exact (hf t (lt_of_lt_of_le hp ht.1) (lt_of_le_of_lt ht.2 hq1)).continuousAt.continuousWithinAt
      · intro t ht
        exact (hf t (lt_of_lt_of_le hp (interior_subset ht).1)
          (lt_of_le_of_lt (interior_subset ht).2 hq1)).hasDerivWithinAt
      · intro t ht
        exact mul_nonneg (sub_nonneg.mpr (interior_subset ht).1)
          (inverse_binary_variance_ge_four (lt_of_lt_of_le hp (interior_subset ht).1)
            (lt_of_le_of_lt (interior_subset ht).2 hq1))
    have h := hm ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
    rw [hpzero] at h
    dsimp [f] at h
    linarith
  · have hm : AntitoneOn f (Icc q p) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q p)
      · intro t ht
        exact (hf t (lt_of_lt_of_le hq ht.1) (lt_of_le_of_lt ht.2 hp1)).continuousAt.continuousWithinAt
      · intro t ht
        exact (hf t (lt_of_lt_of_le hq (interior_subset ht).1)
          (lt_of_le_of_lt (interior_subset ht).2 hp1)).hasDerivWithinAt
      · intro t ht
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (interior_subset ht).2)
          (inverse_binary_variance_ge_four (lt_of_lt_of_le hq (interior_subset ht).1)
            (lt_of_le_of_lt (interior_subset ht).2 hp1))
    have h := hm ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
    rw [hpzero] at h
    dsimp [f] at h
    linarith

/-- Logarithmic AM–GM on an arbitrary nonempty finite group. -/
theorem sum_log_le_card_mul_log_mean {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hs : s.Nonempty) (hr : ∀ i ∈ s, 0 < r i) :
    (∑ i ∈ s, Real.log (r i)) ≤ s.card * Real.log ((∑ i ∈ s, r i) / s.card) := by
  have hk : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hR : 0 < ∑ i ∈ s, r i := sum_pos hr hs
  let a : ℝ := (∑ i ∈ s, r i) / s.card
  have ha : 0 < a := div_pos hR hk
  have hi (i : ι) (his : i ∈ s) : Real.log (r i) - Real.log a ≤ r i / a - 1 := by
    rw [← Real.log_div (hr i his).ne' ha.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hr i his) ha)
  have h := Finset.sum_le_sum hi
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div] at h
  have hsum : (∑ i ∈ s, r i) / a = s.card := by dsimp [a]; field_simp
  rw [hsum] at h
  dsimp [a] at h
  linarith


/-- The normalization identity relating grouped log means to binary entropy. -/
theorem binaryRelativeEntropy_scaled {N k R : ℝ} (hN : 0 < N)
    (hk : 0 < k) (hkN : k < N) (hR : 0 < R) (hRN : R < N) :
    N * binaryRelativeEntropy (k / N) (R / N) =
      -k * Real.log (R / k) - (N - k) * Real.log ((N - R) / (N - k)) := by
  have hk' : 0 < N - k := sub_pos.mpr hkN
  have hR' : 0 < N - R := sub_pos.mpr hRN
  have hpk : 1 - k / N = (N - k) / N := by field_simp
  have hpR : 1 - R / N = (N - R) / N := by field_simp
  rw [binaryRelativeEntropy, hpk, hpR]
  simp only [Real.log_div hk.ne' hN.ne', Real.log_div hR.ne' hN.ne',
    Real.log_div hk'.ne' hN.ne', Real.log_div hR'.ne' hN.ne',
    Real.log_div hR.ne' hk.ne', Real.log_div hR'.ne' hk'.ne']
  field_simp
  ring

/-- A product deficit bounds its logarithm, with the denominator uniform over
all deficits below `delta`. -/
theorem neg_log_one_sub_le {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hrd : rho ≤ delta) (hd : delta < 1) :
    -Real.log (1 - rho) ≤ rho / (1 - delta) := by
  have hr : 0 < 1 - rho := by linarith
  have hden : 0 < 1 - delta := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hr
  have heq : (1 - rho)⁻¹ - 1 = rho / (1 - rho) := by field_simp; ring
  have h1 : -Real.log (1 - rho) ≤ rho / (1 - rho) := by rw [← heq]; linarith
  exact h1.trans (div_le_div_of_nonneg_left hrho hden (by linarith))

/-- Interior subsets: grouped AM–GM followed by the binary entropy estimate. -/
theorem subset_discrepancy_sq_le_neg_log {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIc : Iᶜ.Nonempty) :
    2 * ((∑ i ∈ I, r i) - I.card) ^ 2 ≤
      n * (-Real.log (∏ i, r i)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hk : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI.card_pos
  have hkc : (0 : ℝ) < Iᶜ.card := Nat.cast_pos.mpr hIc.card_pos
  have hcard : (Iᶜ.card : ℝ) = n - I.card := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using Finset.card_le_univ I : I.card ≤ n)]
  have hRI : 0 < ∑ i ∈ I, r i := sum_pos (fun i _ => hr i) hI
  have hRc : 0 < ∑ i ∈ Iᶜ, r i := sum_pos (fun i _ => hr i) hIc
  have hsumc : (∑ i ∈ Iᶜ, r i) = n - ∑ i ∈ I, r i := by
    have h := Finset.sum_add_sum_compl I r
    rw [hsum] at h
    linarith
  have hkN : (I.card : ℝ) < n := by linarith
  have hRN : (∑ i ∈ I, r i) < n := by linarith
  have hgm := add_le_add
    (sum_log_le_card_mul_log_mean I r hI (fun i _ => hr i))
    (sum_log_le_card_mul_log_mean Iᶜ r hIc (fun i _ => hr i))
  rw [Finset.sum_add_sum_compl, hcard, hsumc,
    ← Real.log_prod (fun i _ => (hr i).ne')] at hgm
  have hent := binaryRelativeEntropy_ge_two_sq
    (div_pos hk hnR) ((div_lt_one hnR).mpr hkN)
    (div_pos hRI hnR) ((div_lt_one hnR).mpr hRN)
  have hscaled := binaryRelativeEntropy_scaled hnR hk hkN hRI hRN
  have hlog : (n : ℝ) * binaryRelativeEntropy (I.card / n) ((∑ i ∈ I, r i) / n) ≤
      -Real.log (∏ i, r i) := by linarith
  have h := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hent hnR.le).trans hlog) hnR.le
  have heq : (n : ℝ) * (n * (2 * ((∑ i ∈ I, r i) / n - I.card / n) ^ 2)) =
      2 * ((∑ i ∈ I, r i) - I.card) ^ 2 := by field_simp
  rwa [heq] at h

/-- Every marginal subset has a squared discrepancy controlled by the actual
product deficit. Empty and full subsets are included. -/
theorem subset_discrepancy_sq_le {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n)
    {rho delta : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd : delta < 1)
    (I : Finset (Fin n)) :
    ((∑ i ∈ I, r i) - I.card) ^ 2 ≤ n * rho / (2 * (1 - delta)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden : 0 < 1 - delta := by linarith
  have hb : 0 ≤ (n : ℝ) * rho / (2 * (1 - delta)) := by positivity
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simpa using hb
  rcases Iᶜ.eq_empty_or_nonempty with hfull | hIc
  · have hIu : I = Finset.univ := by
      simpa using congrArg (fun s : Finset (Fin n) => sᶜ) hfull
    simpa [hIu, hsum] using hb
  have hs := subset_discrepancy_sq_le_neg_log hn r hr hsum I hI hIc
  rw [hprod] at hs
  have ht := mul_le_mul_of_nonneg_left (neg_log_one_sub_le hrho hrd hd) hnR.le
  have hfinal : 2 * ((∑ i ∈ I, r i) - I.card) ^ 2 ≤
      n * rho / (1 - delta) := by simpa only [mul_div_assoc] using hs.trans ht
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (1 - delta))).mpr
  have := (le_div_iff₀ hden).mp hfinal
  nlinarith


/-- The subset discrepancy estimate in its geometric square-root form. -/
theorem subset_discrepancy_le {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n)
    {rho delta : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd : delta < 1)
    (I : Finset (Fin n)) :
    |(∑ i ∈ I, r i) - I.card| ≤ Real.sqrt (n * rho / (2 * (1 - delta))) := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact subset_discrepancy_sq_le hn r hr hsum hprod hrho hrd hd I

/-- Cauchy–Schwarz uses the shared product deficit only once. -/
theorem shared_subset_discrepancy_sq_le {n : ℕ} (hn : 0 < n)
    (r c : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = n) (hsumc : ∑ j, c j = n)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd : delta < 1)
    (I J : Finset (Fin n)) :
    (|(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card|) ^ 2 ≤
      n * delta / (1 - delta) := by
  have hrb := subset_discrepancy_sq_le hn r hr hsumr hprodr hrho (by linarith) hd I
  have hcb := subset_discrepancy_sq_le hn c hc hsumc hprodc hsigma (by linarith) hd J
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 1 - delta := by linarith
  have hb : (n : ℝ) * (rho + sigma) / (1 - delta) ≤ n * delta / (1 - delta) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hnR) hden.le
  have heq : (n : ℝ) * (rho + sigma) / (1 - delta) =
      2 * (n * rho / (2 * (1 - delta)) + n * sigma / (2 * (1 - delta))) := by field_simp
  rw [heq] at hb
  have hsq := sq_nonneg (|(∑ i ∈ I, r i) - I.card| - |(∑ j ∈ J, c j) - J.card|)
  have hri := sq_abs ((∑ i ∈ I, r i) - I.card)
  have hcj := sq_abs ((∑ j ∈ J, c j) - J.card)
  nlinarith

/-- Shared row/column subset discrepancy, with all subsets allowed. -/
theorem shared_subset_discrepancy_le {n : ℕ} (hn : 0 < n)
    (r c : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = n) (hsumc : ∑ j, c j = n)
    {rho sigma delta : ℝ} (hprodr : ∏ i, r i = 1 - rho)
    (hprodc : ∏ j, c j = 1 - sigma) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hbudget : rho + sigma ≤ delta) (hd : delta < 1)
    (I J : Finset (Fin n)) :
    |(∑ i ∈ I, r i) - I.card| + |(∑ j ∈ J, c j) - J.card| ≤
      Real.sqrt (n * delta / (1 - delta)) := by
  exact Real.le_sqrt_of_sq_le (shared_subset_discrepancy_sq_le hn r c hr hc
    hsumr hsumc hprodr hprodc hrho hsigma hbudget hd I J)

/-- The actual contender bound uses the permanent deficit `gamma - per A`.
Cell zeros are unrestricted, and marginal positivity is derived internally. -/
theorem dittert_contender_subset_discrepancy {n : ℕ} (hn : 2 ≤ n)
    (A : Board n n) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A)
    (I J : Finset (Fin n)) :
    |(∑ i ∈ I, rowSum A i) - I.card| + |(∑ j ∈ J, colSum A j) - J.card| ≤
      Real.sqrt (n * (dittertConstant n - A.permanent) /
        (1 - (dittertConstant n - A.permanent))) := by
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, _, hdg⟩ := dittert_contender_deficit_budget hn A hA hmass hcont
  exact shared_subset_discrepancy_le (by omega) (rowSum A) (colSum A) hr hc hmass
    (by rwa [← totalMass_eq_sum_colSum]) (by ring) (by ring) hrho hsigma hb
    (hdg.trans_lt (dittertConstant_lt_one hn)) I J

/-- A singleton cap from the generic product-deficit estimate. -/
theorem marginal_le_of_deficit_cap {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n)
    {rho delta H : ℝ} (hprod : ∏ i, r i = 1 - rho)
    (hrho : 0 ≤ rho) (hrd : rho ≤ delta) (hd : delta < 1)
    (hH : 1 ≤ H) (hcap : (n : ℝ) * delta / (2 * (1 - delta)) ≤ (H - 1) ^ 2)
    (i : Fin n) : r i ≤ H := by
  have hs := subset_discrepancy_sq_le hn r hr hsum hprod hrho hrd hd {i}
  simp only [sum_singleton, Finset.card_singleton, Nat.cast_one] at hs
  have hdpos : 0 < 2 * (1 - delta) := by linarith
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrd (Nat.cast_nonneg n)) hdpos.le
  have hsq := hs.trans (hm.trans hcap)
  nlinarith

/-- The exact dimension-seven cap needed by the fourteen-vertex sweep. -/
theorem dittert_contender_marginal_cap_seven (A : Board 7 7)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 7)
    (hcont : 2 - dittertConstant 7 ≤ dittertFunctional A) :
    (∀ i, rowSum A i ≤ 23 / 20) ∧ (∀ j, colSum A j ≤ 23 / 20) := by
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, _, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hcap : (7 : ℝ) * dittertConstant 7 / (2 * (1 - dittertConstant 7)) ≤
      (23 / 20 - 1 : ℝ) ^ 2 := by norm_num [dittertConstant, Nat.factorial]
  constructor
  · exact marginal_le_of_deficit_cap (by norm_num) (rowSum A) hr hmass (by ring)
      hrho (by linarith) (dittertConstant_lt_one (by norm_num)) (by norm_num) hcap
  · exact marginal_le_of_deficit_cap (by norm_num) (colSum A) hc
      (by rwa [← totalMass_eq_sum_colSum]) (by ring)
      hsigma (by linarith) (dittertConstant_lt_one (by norm_num)) (by norm_num) hcap

end
end DittertRybin
