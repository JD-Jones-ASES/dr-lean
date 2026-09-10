import DR.Endpoint.NearEndpointCutFloors
import DR.Endpoint.NearEndpointParameters
import DR.Endpoint.BoundaryScalingScalars

/-! Actual near-endpoint boundary exclusion conditional on an explicitly
stated permanent floor for doubly stochastic matrices with two independent
zeros. No permanent floor is assumed by a principal theorem here. -/
namespace DittertRybin

/-- A direct permanent bound on the full closed two-independent-zero domain. -/
def TwoIndependentZeroPermanentBound (N : ℕ) (v : ℝ) : Prop :=
  ∀ D : Board N N, D ∈ doublyStochastic ℝ (Fin N) →
    (∃ i₁ i₂ j₁ j₂, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ D i₁ j₁=0 ∧ D i₂ j₂=0) →
      v ≤ D.permanent

theorem nearEndpoint_zero_of_positive_domination {n : ℕ} {P B : Board n n}
    {c : ℝ} (hc : 0 < c) (hB : ∀ i j, 0 ≤ B i j)
    (hdom : ∀ i j, c*B i j ≤ P i j) (hz : ∃ i j, P i j=0) :
    ∃ i j, B i j=0 := by
  obtain ⟨i,j,hij⟩ := hz
  refine ⟨i,j,?_⟩
  have h := hdom i j
  rw [hij] at h
  have hb := hB i j
  nlinarith

theorem nearEndpointRookRatio_of_scaled_lower {n : ℕ} {P B : Board n n}
    {c beta : ℝ} (hc : 0 ≤ c) (hB : ∀ i j, 0 ≤ B i j)
    (hdom : ∀ i j, c*B i j ≤ P i j) (hbeta : beta ≤ nearEndpointRookRatio B) :
    c^(n-1)*beta ≤ nearEndpointRookRatio P := by
  have hmono := nearEndpointRookRatio_mono (B := c • B) (P := P)
    (fun i j => mul_nonneg hc (hB i j)) hdom
  rw [nearEndpointRookRatio_smul] at hmono
  exact (mul_le_mul_of_nonneg_left hbeta (pow_nonneg hc _)).trans hmono

theorem nearEndpoint_padding_floor_of_twoZeros {n : ℕ} (hn : 1 ≤ n)
    {v : ℝ} (hfloor : TwoIndependentZeroPermanentBound (n+1) v)
    {B : Board n n} (hB : IsProbability B)
    (hr : ∀ i, rowSum B i=1/(n : ℝ)) (hc : ∀ j, colSum B j=1/(n : ℝ))
    (hz : ∃ i j, B i j=0) : v ≤ (nearEndpointPadding B).permanent :=
  hfloor _ (nearEndpointPadding_mem_doublyStochastic (by omega) hB.1 hr hc)
    (nearEndpointPadding_two_independent_zeros hz)

/-- Every boundary contender in the infinite range contradicts the actual
permanent floor and the already proved shared-deficit scaling inequality. -/
theorem nearEndpoint_boundary_contender_impossible_tail {n : ℕ} (hn : 26 ≤ n)
    (hfloor : TwoIndependentZeroPermanentBound (n+1)
      (boundaryPermanentFloor (n+1)*(1+1/(4*((n : ℝ)-1)^2))))
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (hz : ∃ i j, P i j=0) : False := by
  obtain ⟨ha,hsize,hgap⟩ := nearEndpoint_parameter_bounds hn
  obtain ⟨t,B,ht,ht1,htsq,hB,hr,hc,hdom⟩ :=
    nearEndpoint_contender_exists_balanced_domination (by omega) hP hcont ha.le hsize
  have hzB := nearEndpoint_zero_of_positive_domination (sub_pos.mpr ht1) hB.1 hdom hz
  have hper := nearEndpoint_padding_floor_of_twoZeros (by omega : 1 ≤ n) hfloor hB hr hc hzB
  have hrook := nearEndpointRookRatio_lower_of_padding (by omega : 2 ≤ n) B hper
  have hmu := boundaryPermanentFloor_pos (by omega : 3 ≤ n+1)
  have hcancel : distinctUniformProbability n (n-1)*
      (boundaryPermanentFloor (n+1)*(1+1/(4*((n : ℝ)-1)^2)))/boundaryPermanentFloor (n+1) =
      distinctUniformProbability n (n-1)*(1+1/(4*((n : ℝ)-1)^2)) := by field_simp
  rw [hcancel] at hrook
  have hbound := nearEndpointRookRatio_of_scaled_lower (sub_nonneg.mpr ht1.le) hB.1 hdom hrook
  have hdef : nearEndpointRookRatio P = distinctUniformProbability n (n-1)-nearEndpointRookDeficit P := by
    unfold nearEndpointRookDeficit
    ring
  rw [hdef] at hbound
  obtain ⟨_,_,_,hd,_⟩ := nearEndpoint_contender_deficit_budget (by omega) hP hcont
  have hM : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hbeta : 0 < 1+1/(4*((n : ℝ)-1)^2) := by positivity
  apply endpoint_boundary_scaling_contradiction (m := n-1)
    (distinctUniformProbability_pos (by omega) (Nat.sub_le n 1)) hbeta
    (by positivity) hd ht ht1.le htsq hgap
  nlinarith only [hbound]

end DittertRybin
