import DR.Endpoint.TwoZeroPolynomialBounds
import DR.Endpoint.NearEndpointCutChecks

/-! The five exact rational cubic brackets now have a real scalar meaning:
their permanent references lie strictly below every feasible two-parameter
permanent. An arbitrary-matrix face reduction remains a separate theorem. -/
namespace DittertRybin.Certificates

@[simp] theorem nearEndpointCubicRat_cast (m : ℕ) (u : ℚ) :
    (nearEndpointCubicRat m u : ℝ) = twoZeroCubic m (u : ℝ) := by
  simp [nearEndpointCubicRat,twoZeroCubic]

@[simp] theorem nearEndpointTwoZeroXRat_cast (m : ℕ) (u : ℚ) :
    (nearEndpointTwoZeroXRat m u : ℝ) = twoZeroX m (u : ℝ) := by
  simp [nearEndpointTwoZeroXRat,twoZeroX]

@[simp] theorem nearEndpointTwoZeroHRat_cast (m : ℕ) (u : ℚ) :
    (nearEndpointTwoZeroHRat m u : ℝ) = twoZeroH m (u : ℝ) := by
  simp [nearEndpointTwoZeroHRat,twoZeroH]

end DittertRybin.Certificates

namespace DittertRybin
open Certificates

/-- Exact finite references interpreted on the full feasible parameter square. -/
theorem nearEndpoint_twoZeroReducedPermanent_finite_lt {n : ℕ}
    (hn : 21 ≤ n) (hn' : n ≤ 25) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/((n-1 : ℕ) : ℝ)) (hbM : b ≤ 1/((n-1 : ℕ) : ℝ)) :
    (nearEndpointPermanentFloorRat n : ℝ) < twoZeroReducedPermanent (n-1) a b := by
  obtain ⟨hl,hlr,hr,hfl,hfr,_,hfloor⟩ := nearEndpointBracketCertificate_checked hn hn'
  have hlR : (0 : ℝ) < (nearEndpointRootLeft n : ℝ) := by exact_mod_cast hl
  have hlrR : (nearEndpointRootLeft n : ℝ) < (nearEndpointRootRight n : ℝ) := by
    exact_mod_cast hlr
  have hrR : (nearEndpointRootRight n : ℝ) < 1/((n-1 : ℕ) : ℝ) := by
    have h : (nearEndpointRootRight n : ℝ) < ((1/((n-1 : ℕ) : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hr
    simpa using h
  have hflR : twoZeroCubic (n-1) (nearEndpointRootLeft n : ℝ) < 0 := by
    rw [← nearEndpointCubicRat_cast]
    exact_mod_cast hfl
  have hfrR : 0 < twoZeroCubic (n-1) (nearEndpointRootRight n : ℝ) := by
    rw [← nearEndpointCubicRat_cast]
    exact_mod_cast hfr
  have hfloorR : (nearEndpointPermanentFloorRat n : ℝ) <
      (((n-1).factorial : ℚ)*(nearEndpointTwoZeroXRat (n-1) (nearEndpointRootLeft n))^((n-1)-2)*
        nearEndpointTwoZeroHRat (n-1) (nearEndpointRootRight n) : ℚ) := by
    exact_mod_cast hfloor
  simp only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow,nearEndpointTwoZeroXRat_cast,
    nearEndpointTwoZeroHRat_cast] at hfloorR
  exact hfloorR.trans_le (twoZeroReducedPermanent_lower_of_bracket (by omega : 4 ≤ n-1)
    ha hb haM hbM hlR.le hlrR.le hrR.le hflR.le hfrR.le)

end DittertRybin
