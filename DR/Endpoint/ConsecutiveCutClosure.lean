import DR.Endpoint.ConsecutiveCutTransport
import DR.Endpoint.ConsecutiveCutScalars

/-! Every boundary contender in the eleven finite consecutive dimensions is
excluded using an actual minimum dilation and its active zero rectangle. -/

namespace DittertRybin
open scoped BigOperators

theorem consecutive_boundary_contender_impossible {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29)
    {P : Board m (m+1)} (hP : IsProbability P)
    (hcont : uniformSeparationValue m (m+1) m ≤ separationProbability P m)
    (hz : ∃ i j, P i j = 0) : False := by
  classical
  have hb := distinctUniformProbability_pos (by omega : 0 < m+1) (by omega : m ≤ m+1)
  have hb1 := distinctUniformProbability_lt_one (by omega : 0 < m+1) (by omega : 2 ≤ m)
  have hden : 0 < 1-distinctUniformProbability (m+1) m := by linarith
  have hd := (endpoint_contender_deficit_budget (by omega) (by omega) hP hcont).2.2.2.1
  obtain ⟨q, B, I, J, hq, hq1, hB, hr, hc, hdom, hp, hactive, hzero⟩ :=
    exists_minimum_rectangular_dilation (by omega) (by omega) hP
      (consecutive_contender_positive_cut hm hm' hP hcont)
  have hzB : ∃ i j, B i j = 0 := by
    obtain ⟨i, j, hij⟩ := hz
    refine ⟨i, j, ?_⟩
    have h := hdom i j
    rw [hij] at h
    have hpB := mul_nonneg hq.le (hB.1 i j)
    have heq : q*B i j = 0 := le_antisymm h hpB
    exact (mul_eq_zero.mp heq).resolve_left hq.ne'
  by_cases hqeq : q = 1
  · have hPB : P = B := probability_eq_of_entrywise_le hP hB (by simpa [hqeq] using hdom)
    have hfloor := endpointRookRatio_boundary_lower_bound (by omega) (by omega) (by omega)
      hB.1 hr hc hzB
    have hstrict : 1 < boundaryPermanentRatio (m+1) := by
      have h := boundaryPermanentRatio_sub_one_lower (by omega : 4 ≤ m+1)
      have hnR : (1 : ℝ) < ((m+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < m+1)
      have hnpos : 0 < ((m+1 : ℕ) : ℝ)-1 := by linarith
      have hp' : 0 < 1/(3*(((m+1 : ℕ) : ℝ)-1)^2) := by positivity
      linarith
    have hmul := mul_lt_mul_of_pos_left hstrict hb
    rw [hPB, endpointRookDeficit] at hd
    nlinarith only [hfloor, hmul, hd]
  have hqstrict : q < 1 := lt_of_le_of_ne hq1 hqeq
  have hk : I.card ≤ m := by simpa using I.card_le_univ
  have hl : J.card ≤ m+1 := by simpa using J.card_le_univ
  have hcards : I.card ≠ m ∨ J.card ≠ m+1 := by
    by_contra h
    push Not at h
    have hi : I = Finset.univ := I.card_eq_iff_eq_univ.mp (by simpa using h.1)
    have hj : J = Finset.univ := J.card_eq_iff_eq_univ.mp (by simpa using h.2)
    rw [hi, hj, rectangularCutDemand_univ (by omega) (by omega), mul_one] at hactive
    change totalMass P = q at hactive
    rw [hP.2] at hactive
    linarith
  let C := endpointSizedCutCoefficient (101/100) m (m+1) I.card J.card
  let beta := endpointConsecutiveCutRookFloor m (m+1) I.card J.card
  have hC : 0 ≤ C := endpointSizedCutCoefficient_nonneg (by omega) hk hl _
  have hgap := (consecutiveCut_real_certificate hm hm' hk hl (by simpa [rectangularCutDemand] using hp) hcards).2
  change beta-distinctUniformProbability (m+1) m-(m : ℝ)^2*C*beta^2/
    (4*(1-distinctUniformProbability (m+1) m)) > distinctUniformProbability (m+1) m/2000 at hgap
  have hfloor := endpointRookRatio_sized_boundary_lower_bound (by omega) (by omega) (by omega)
    hB hr hc hzB I J hp hzero
  have hscaled := mul_le_mul_of_nonneg_left hfloor (pow_nonneg hq.le m)
  have hmono := endpointRookRatio_mono (B := q • B)
    (fun i j => mul_nonneg hq.le (hB.1 i j)) hdom
  rw [endpointRookRatio_smul] at hmono
  have hboundary : q^m*beta ≤ distinctUniformProbability (m+1) m-endpointRookDeficit P := by
    simpa only [endpointRookDeficit, sub_sub_cancel] using hscaled.trans hmono
  have ht := consecutive_active_cut_dilation_sq hm hm' hP hcont I J hq1 hp hactive
  apply endpoint_sized_scaling_contradiction (m := m) (beta := beta)
    (L := C/(1-distinctUniformProbability (m+1) m)) hb (div_nonneg hC hden.le) hd
    (by linarith : 0 ≤ 1-q) (by linarith : 1-q ≤ 1)
  · exact ht.trans_eq (by ring)
  · have hb2000 : 0 < distinctUniformProbability (m+1) m/2000 := by positivity
    apply (lt_trans hb2000 hgap).trans_eq
    field_simp
  · simpa only [sub_sub_cancel] using hboundary

end DittertRybin
