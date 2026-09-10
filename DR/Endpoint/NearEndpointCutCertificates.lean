import DR.Endpoint.NearEndpointCutChecks

/-! Exact scalar gates interpreted as the actual real cut coefficient and
normalized padding floor. No universal permanent claim is inferred here. -/
namespace DittertRybin
open Certificates

/-- Every admissible finite cut has both a strict positive-dilation margin
and the strict square-completion margin needed by the actual matrix proof. -/
theorem nearEndpointCut_real_certificate {n k l : ℕ} (hn : 21≤n) (hn' : n≤25)
    (hk : k≤n) (hl : l≤n) (hp : n<k+l) (hwhole : k≠n ∨ l≠n) :
    nearEndpointSizedCutCoefficient n k l*distinctUniformProbability n (n-1)/
        (1-distinctUniformProbability n (n-1)) < 1/10000 ∧
      nearEndpointCutRookFloor n (nearEndpointPermanentFloorRat n : ℝ) k l-
        distinctUniformProbability n (n-1)-
        ((n-1 : ℕ) : ℝ)^2*nearEndpointSizedCutCoefficient n k l*
          (nearEndpointCutRookFloor n (nearEndpointPermanentFloorRat n : ℝ) k l)^2/
          (4*(1-distinctUniformProbability n (n-1))) >
        3*distinctUniformProbability n (n-1)/10000 := by
  obtain ⟨hsmall,hgap⟩ := nearEndpointCutCertificate_checked hn hn' hk hl hp hwhole
  constructor
  · have h : ((nearEndpointCutRat n k l*nearEndpointAvoidanceRat n/
        (1-nearEndpointAvoidanceRat n) : ℚ) : ℝ)<((1/10000 : ℚ) : ℝ) := by
      exact_mod_cast hsmall
    simpa using h
  · have h : ((nearEndpointCutRookFloorRat n k l-nearEndpointAvoidanceRat n-
        ((n-1 : ℕ) : ℚ)^2*nearEndpointCutRat n k l*(nearEndpointCutRookFloorRat n k l)^2/
        (4*(1-nearEndpointAvoidanceRat n)) : ℚ) : ℝ)>
        ((3*nearEndpointAvoidanceRat n/10000 : ℚ) : ℝ) := by
      exact_mod_cast hgap
    simpa using h

/-- The certified two-zero reference exceeds the one-zero boundary reference. -/
theorem nearEndpointPermanentFloorRat_gt_boundary {n : ℕ} (hn : 21≤n) (hn' : n≤25) :
    boundaryPermanentFloor (n+1) < (nearEndpointPermanentFloorRat n : ℝ) := by
  have heQ := (nearEndpointBracketCertificate_checked hn hn').2.2.2.2.2.1
  have he : (0 : ℝ)<(nearEndpointExcessRat n : ℝ) := by exact_mod_cast heQ
  have hmu := boundaryPermanentFloor_pos (by omega : 3≤n+1)
  simp only [nearEndpointPermanentFloorRat,Rat.cast_mul,Rat.cast_add,Rat.cast_one,
    nearEndpointBoundaryRat_cast]
  nlinarith only [mul_pos hmu he]

end DittertRybin
