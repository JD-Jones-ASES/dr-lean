import DR.Endpoint.ConsecutiveCutCertificates

/-! Actual cut positivity and the exact active-cut dilation loss. All finite
certificate inputs have already been discharged on the literal range. -/

namespace DittertRybin
open scoped BigOperators

theorem endpointSizedCutCoefficient_nonneg {m n k l : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ m) (hl : l ≤ n) (H : ℝ) :
    0 ≤ endpointSizedCutCoefficient H m n k l := by
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hlR : (l : ℝ) ≤ n := by exact_mod_cast hl
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ dittertConstant m := by unfold dittertConstant; positivity
  have hb : 0 ≤ distinctUniformProbability n m := by
    unfold distinctUniformProbability
    positivity
  unfold endpointSizedCutCoefficient endpointSizedRowCutCoefficient endpointSizedColumnCutCoefficient
  positivity

theorem consecutive_contender_positive_cut {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29)
    {P : Board m (m+1)} (hP : IsProbability P)
    (hcont : uniformSeparationValue m (m+1) m ≤ separationProbability P m)
    (I : Finset (Fin m)) (J : Finset (Fin (m+1)))
    (hp : 0 < rectangularCutDemand I J) : 0 < cutMass P I J := by
  classical
  by_cases hwhole : I = Finset.univ ∧ J = Finset.univ
  · rcases hwhole with ⟨rfl, rfl⟩
    change 0 < totalMass P
    rw [hP.2]
    norm_num
  have hk : I.card ≤ m := by simpa using I.card_le_univ
  have hl : J.card ≤ m+1 := by simpa using J.card_le_univ
  have hcards : I.card ≠ m ∨ J.card ≠ m+1 := by
    by_contra h
    push Not at h
    apply hwhole
    exact ⟨I.card_eq_iff_eq_univ.mp (by simpa using h.1),
      J.card_eq_iff_eq_univ.mp (by simpa using h.2)⟩
  let p := rectangularCutDemand I J
  let C := endpointSizedCutCoefficient (101/100) m (m+1) I.card J.card
  let b := distinctUniformProbability (m+1) m
  let d := endpointRookDeficit P
  let E := |(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/((m+1 : ℕ) : ℝ)|
  change 0 < p at hp
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := endpointSizedCutCoefficient_nonneg (by omega) hk hl _
  have hb1 : b < 1 := distinctUniformProbability_lt_one (by omega) (by omega)
  have hden : 0 < 1-b := by linarith
  have hdb : d ≤ b := (endpoint_contender_deficit_budget (by omega) (by omega) hP hcont).2.2.2.2
  have hsmall := (consecutiveCut_real_certificate hm hm' hk hl (by simpa [p, rectangularCutDemand] using hp) hcards).1
  change C*b/(1-b) < 1/500 at hsmall
  have hdev := endpoint_contender_sized_cut_discrepancy_sq (by omega) (by omega) hP hcont
    (by norm_num : (1 : ℝ) ≤ 101/100) (consecutiveCut_row_cap hm hm') I J hp
  change E^2 ≤ p^2*C*d/(1-b) at hdev
  have hdev' : E^2 ≤ p^2*(C*d/(1-b)) := hdev.trans_eq (by ring)
  have hbound : E^2 < p^2 := by
    have hmul := mul_le_mul_of_nonneg_left hdb hC
    have hdiv := div_le_div_of_nonneg_right hmul hden.le
    have hs := mul_lt_mul_of_pos_left hsmall (sq_pos_of_pos hp)
    have hm := mul_le_mul_of_nonneg_left hdiv (sq_nonneg p)
    nlinarith only [hdev', hs, hm, sq_pos_of_pos hp]
  have hEp : E < p := by nlinarith only [hbound, hE, hp]
  have hcut := cutMass_lower_of_subset_discrepancy hP I J (le_rfl : E ≤ E)
  change p-E ≤ cutMass P I J at hcut
  linarith

theorem consecutive_active_cut_dilation_sq {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29)
    {P : Board m (m+1)} (hP : IsProbability P)
    (hcont : uniformSeparationValue m (m+1) m ≤ separationProbability P m)
    (I : Finset (Fin m)) (J : Finset (Fin (m+1))) {q : ℝ}
    (hq : q ≤ 1) (hp : 0 < rectangularCutDemand I J)
    (hactive : cutMass P I J = q*rectangularCutDemand I J) :
    (1-q)^2 ≤ endpointSizedCutCoefficient (101/100) m (m+1) I.card J.card*
      endpointRookDeficit P/(1-distinctUniformProbability (m+1) m) := by
  let p := rectangularCutDemand I J
  let E := |(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/((m+1 : ℕ) : ℝ)|
  have hcut := cutMass_lower_of_subset_discrepancy hP I J (le_rfl : E ≤ E)
  change p-E ≤ cutMass P I J at hcut
  have hlin : p*(1-q) ≤ E := by rw [hactive] at hcut; dsimp [p] at *; nlinarith
  have hnonneg : 0 ≤ p*(1-q) := mul_nonneg hp.le (sub_nonneg.mpr hq)
  have hsq := pow_le_pow_left₀ hnonneg hlin 2
  have hdev := endpoint_contender_sized_cut_discrepancy_sq (by omega) (by omega) hP hcont
    (by norm_num : (1 : ℝ) ≤ 101/100) (consecutiveCut_row_cap hm hm') I J hp
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hp)).mp
  have hdev' : E^2 ≤ p^2 *
      (endpointSizedCutCoefficient (101/100) m (m+1) I.card J.card*
        endpointRookDeficit P/(1-distinctUniformProbability (m+1) m)) :=
    hdev.trans_eq (by dsimp [p, rectangularCutDemand]; ring)
  change p^2*(1-q)^2 ≤ p^2*_
  nlinarith only [hsq, hdev']

end DittertRybin
