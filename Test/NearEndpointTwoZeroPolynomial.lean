import DR.Endpoint.NearEndpointTwoZeroPolynomial

namespace DittertRybin.Tests
open Certificates

-- The first finite case permits both borders to vanish.
example : (nearEndpointPermanentFloorRat 21 : ℝ) < twoZeroReducedPermanent 20 0 0 := by
  exact nearEndpoint_twoZeroReducedPermanent_finite_lt (by norm_num : 21 ≤ 21)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The last finite case permits both exceptional diagonals to vanish.
example : (nearEndpointPermanentFloorRat 25 : ℝ) < twoZeroReducedPermanent 24 (1/24) (1/24) := by
  exact nearEndpoint_twoZeroReducedPermanent_finite_lt (by norm_num : 21 ≤ 25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Cast transport is an identity for signed scores, outside the bracket too.
example : (nearEndpointCubicRat 20 (-3/7) : ℝ) = twoZeroCubic 20 (-3/7) ∧
    (nearEndpointTwoZeroHRat 20 (-3/7) : ℝ) = twoZeroH 20 (-3/7) := by
  constructor <;> simp

-- Dropping the parameter bound is false: this infeasible point gives zero.
example : twoZeroReducedPermanent 20 1 0 = 0 ∧
    ¬(nearEndpointPermanentFloorRat 21 : ℝ) ≤ twoZeroReducedPermanent 20 1 0 := by
  norm_num [twoZeroReducedPermanent,nearEndpointPermanentFloorRat,nearEndpointBoundaryRat,
    nearEndpointExcessRat,Nat.factorial]

example {n : ℕ} (hn : 21 ≤ n) (hn' : n ≤ 25) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ 1/((n-1 : ℕ) : ℝ))
    (hbM : b ≤ 1/((n-1 : ℕ) : ℝ)) :
    (nearEndpointPermanentFloorRat n : ℝ) < twoZeroReducedPermanent (n-1) a b :=
  nearEndpoint_twoZeroReducedPermanent_finite_lt hn hn' ha hb haM hbM

#print axioms nearEndpointCubicRat_cast
#print axioms nearEndpointTwoZeroHRat_cast
#print axioms nearEndpoint_twoZeroReducedPermanent_finite_lt
end DittertRybin.Tests
