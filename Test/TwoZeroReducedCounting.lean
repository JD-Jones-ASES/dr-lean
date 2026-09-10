import DR.Endpoint.TwoZeroReducedCounting
import DR.Square.OrderThree

namespace DittertRybin.Tests

-- Base ordinary count two, with both exceptional diagonals and the core zero.
example : (twoZeroReducedBoard 2 (1/2) (1/2)).permanent = 1/4 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]

-- A disconnected boundary board and a single zero exceptional diagonal.
example : (twoZeroReducedBoard 2 0 0).permanent = 1/2 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]
example : (twoZeroReducedBoard 2 0 (1/2)).permanent = 1/4 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]

-- Both signs of actual entries, and a negative permanent, are retained.
example : (twoZeroReducedBoard 2 1 (-1)).permanent = 13/2 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]
example : (twoZeroReducedBoard 3 1 1).permanent = -188/9 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]

-- Dropping the n! factor changes an actual boundary permanent.
example : (twoZeroReducedBoard 2 (1/2) (1/2)).permanent ≠ 1/8 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]

-- The order-three permanent is computed independently; it rejects n=1.
private theorem reduced_one_direct :
    (twoZeroReducedBoard 1 (1/4) (1/4)).permanent = 3/8 := by
  have h := permanent_three (twoZeroReducedBoard 1 (1/4) (1/4))
  norm_num [twoZeroReducedBoard,Fin.ext_iff] at h
  exact h
example : (twoZeroReducedBoard 1 (1/4) (1/4)).permanent ≠
    twoZeroReducedPermanent 1 (1/4) (1/4) := by
  rw [reduced_one_direct]
  norm_num [twoZeroReducedPermanent]

-- Core-zero algebra keeps the n=2 zeroth power and n>2 positive powers distinct.
example : (twoZeroReducedBoard 3 (1/2) (1/2)).permanent = 0 := by
  rw [twoZeroReducedBoard_permanent (by decide)]
  norm_num [twoZeroReducedPermanent]

-- Signed parameters remain quantified, with no feasibility premise.
example {n : ℕ} (hn : 2≤n) (a b : ℝ) :
    (twoZeroReducedBoard n a b).permanent = twoZeroReducedPermanent n a b :=
  twoZeroReducedBoard_permanent hn a b

#print axioms twoZeroReducedBoard_permanent
end DittertRybin.Tests
