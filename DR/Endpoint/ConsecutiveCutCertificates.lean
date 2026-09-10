import DR.Certificates.ConsecutiveCutChecks
import DR.Endpoint.ConsecutiveCutFloors

/-! Exact finite rational gates interpreted as the real cut coefficients and
the actual balanced-board rook floor. -/

namespace DittertRybin
open Certificates

@[simp] theorem consecutiveRookFloorRat_cast (m n k l : ℕ) :
    (consecutiveRookFloorRat m n k l : ℝ) = endpointConsecutiveCutRookFloor m n k l := by
  by_cases h : k < m ∧ l < n <;>
    simp [consecutiveRookFloorRat, endpointConsecutiveCutRookFloor,
      endpointConsecutiveRectangleFloor, h]

theorem consecutiveCut_row_cap {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29) :
    (m : ℝ)*distinctUniformProbability (m+1) m /
      (2*(1-distinctUniformProbability (m+1) m)) ≤ (101/100-1 : ℝ)^2 := by
  have h := consecutiveCut_row_cap_checked hm hm'
  have hc : ((m : ℚ)*consecutiveAvoidanceRat m (m+1) /
      (2*(1-consecutiveAvoidanceRat m (m+1))) : ℝ) ≤ ((101/100-1 : ℚ)^2 : ℝ) := by
    exact_mod_cast h
  simpa using hc

theorem consecutiveCut_real_certificate {m k l : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29)
    (hk : k ≤ m) (hl : l ≤ m+1)
    (hp : 0 < (k : ℝ)/m+(l : ℝ)/(m+1)-1) (hwhole : k ≠ m ∨ l ≠ m+1) :
    endpointSizedCutCoefficient (101/100) m (m+1) k l *
        distinctUniformProbability (m+1) m/(1-distinctUniformProbability (m+1) m) < 1/500 ∧
    endpointConsecutiveCutRookFloor m (m+1) k l-distinctUniformProbability (m+1) m-
      (m : ℝ)^2*endpointSizedCutCoefficient (101/100) m (m+1) k l*
        (endpointConsecutiveCutRookFloor m (m+1) k l)^2/
          (4*(1-distinctUniformProbability (m+1) m)) >
      distinctUniformProbability (m+1) m/2000 := by
  have hpQ : 0 < consecutiveDemandRat m (m+1) k l := by
    have hc : (0 : ℝ) < (consecutiveDemandRat m (m+1) k l : ℝ) := by simpa using hp
    exact_mod_cast hc
  obtain ⟨hsmall, hgap⟩ := consecutiveCutCertificate_checked hm hm' hk hl hpQ hwhole
  constructor
  · have hc : ((consecutiveCutRat m (m+1) k l*consecutiveAvoidanceRat m (m+1)/
        (1-consecutiveAvoidanceRat m (m+1)) : ℚ) : ℝ) < ((1/500 : ℚ) : ℝ) := by
      exact_mod_cast hsmall
    simpa using hc
  · have hc : (((consecutiveRookFloorRat m (m+1) k l-consecutiveAvoidanceRat m (m+1)-
        (m : ℚ)^2*consecutiveCutRat m (m+1) k l*(consecutiveRookFloorRat m (m+1) k l)^2/
          (4*(1-consecutiveAvoidanceRat m (m+1)))) : ℚ) : ℝ) >
        ((consecutiveAvoidanceRat m (m+1)/2000 : ℚ) : ℝ) := by
      exact_mod_cast hgap
    simpa using hc

end DittertRybin
