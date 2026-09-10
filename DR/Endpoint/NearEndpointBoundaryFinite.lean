import DR.Endpoint.NearEndpointBoundaryTail
import DR.Endpoint.NearEndpointTransportParameters
import DR.Endpoint.NearEndpointCutCertificates
import DR.Endpoint.ConsecutiveCutScalars

/-! The finite n=21,...,25 boundary exclusion uses an actual minimum dilation,
its active complementary zero rectangle, and all checked ordered cut gates.
The two-independent-zero permanent floor remains an explicit matrix premise. -/
namespace DittertRybin
open Certificates

theorem nearEndpoint_boundary_contender_impossible_finite {n : ℕ}
    (hn : 21 ≤ n) (hn' : n ≤ 25)
    (hfloor : TwoIndependentZeroPermanentBound (n+1) (nearEndpointPermanentFloorRat n : ℝ))
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (hz : ∃ i j, P i j=0) : False := by
  classical
  obtain ⟨ha,hsize⟩ := nearEndpoint_transport_parameter_bounds hn
  obtain ⟨q,B,I,J,hq,hq1,hB,hr,hc,hdom,hp,hactive,hzero,htsq⟩ :=
    nearEndpoint_contender_exists_active_dilation (by omega) hP hcont ha hsize
  have hapos := distinctUniformProbability_pos (by omega : 0 < n) (Nat.sub_le n 1)
  have ha1 : distinctUniformProbability n (n-1) < 1 := ha.trans_lt (by norm_num)
  have hden : 0 < 1-distinctUniformProbability n (n-1) := by linarith
  have hmu := boundaryPermanentFloor_pos (by omega : 3 ≤ n+1)
  have hzB := nearEndpoint_zero_of_positive_domination hq hB.1 hdom hz
  have hper := nearEndpoint_padding_floor_of_twoZeros (by omega : 1 ≤ n) hfloor hB hr hc hzB
  have hd := (nearEndpoint_contender_deficit_budget (by omega) hP hcont).2.2.2.1
  by_cases hqeq : q=1
  · have hrook := nearEndpointRookRatio_lower_of_padding (by omega : 2 ≤ n) B hper
    have hbound := nearEndpointRookRatio_of_scaled_lower hq.le hB.1 hdom hrook
    rw [hqeq,one_pow,one_mul] at hbound
    have hstrict : distinctUniformProbability n (n-1) <
        distinctUniformProbability n (n-1)*(nearEndpointPermanentFloorRat n : ℝ)/boundaryPermanentFloor (n+1) := by
      apply (lt_div_iff₀ hmu).mpr
      exact mul_lt_mul_of_pos_left (nearEndpointPermanentFloorRat_gt_boundary hn hn') hapos
    unfold nearEndpointRookDeficit at hd
    linarith
  have hk : I.card ≤ n := by simpa using I.card_le_univ
  have hl : J.card ≤ n := by simpa using J.card_le_univ
  have hwhole : I.card≠n ∨ J.card≠n := by
    by_contra h
    push Not at h
    have hi : I=Finset.univ := I.card_eq_iff_eq_univ.mp (by simpa using h.1)
    have hj : J=Finset.univ := J.card_eq_iff_eq_univ.mp (by simpa using h.2)
    rw [hi,hj,rectangularCutDemand_univ (by omega) (by omega),mul_one] at hactive
    change totalMass P=q at hactive
    rw [hP.2] at hactive
    exact hqeq hactive.symm
  have hsum : n < I.card+J.card := by
    rw [rectangularCutDemand_square I J (by omega)] at hp
    have hpos := (div_pos_iff_of_pos_right (show (0 : ℝ) < n by positivity)).mp hp
    have h : (n : ℝ) < (I.card : ℝ)+J.card := by linarith
    exact_mod_cast h
  have hC : 0 ≤ nearEndpointSizedCutCoefficient n I.card J.card := by
    have hkR : (I.card : ℝ) ≤ n := by exact_mod_cast hk
    have hlR : (J.card : ℝ) ≤ n := by exact_mod_cast hl
    have hki : 0 ≤ (n : ℝ)-I.card := by linarith
    have hlj : 0 ≤ (n : ℝ)-J.card := by linarith
    unfold nearEndpointSizedCutCoefficient
    positivity
  let beta := nearEndpointCutRookFloor n (nearEndpointPermanentFloorRat n : ℝ) I.card J.card
  have hgap := (nearEndpointCut_real_certificate hn hn' hk hl hsum hwhole).2
  have hrook := nearEndpointRookRatio_sized_lower_bound (by omega : 2 ≤ n) hB hr hc I J hp hzero hper
  have hbound := nearEndpointRookRatio_of_scaled_lower hq.le hB.1 hdom hrook
  have hboundary : q^(n-1)*beta ≤ distinctUniformProbability n (n-1)-nearEndpointRookDeficit P := by
    simpa only [nearEndpointRookDeficit,sub_sub_cancel] using hbound
  apply endpoint_sized_scaling_contradiction (m := n-1) (beta := beta)
    (L := nearEndpointSizedCutCoefficient n I.card J.card/(1-distinctUniformProbability n (n-1)))
    hapos (div_nonneg hC hden.le) hd (sub_nonneg.mpr hq1) (by linarith : 1-q ≤ 1)
  · exact htsq.trans_eq (by ring)
  · have hsmall : 0 < 3*distinctUniformProbability n (n-1)/10000 := by positivity
    apply (lt_trans hsmall hgap).trans_eq
    dsimp [beta]
    field_simp
  · simpa only [sub_sub_cancel] using hboundary

end DittertRybin
