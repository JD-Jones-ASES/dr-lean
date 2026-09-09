import DR.Rectangular.ThreeRowSupportNormal

namespace DittertRybin.Tests.ThreeRowSupportNormal
open scoped BigOperators

private def boundaryBoard : Board 2 3 := ![![1, 3, 0], ![0, 0, 2]]

-- Unequal columns with the same actual support have a strict, exact norm drop.
example : orderThreeSquareSum boundaryBoard = 14 := by
  norm_num [orderThreeSquareSum, boundaryBoard, Fin.sum_univ_succ]

example : orderThreeSquareSum (blendColumns boundaryBoard 0 1 (1 / 2)) = 12 := by
  rw [orderThreeSquareSum_blend_midpoint boundaryBoard 0 1 (by decide)]
  norm_num [orderThreeSquareSum, boundaryBoard, Fin.sum_univ_succ]

example : SameSupportFloor boundaryBoard 1 boundaryBoard := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [boundaryBoard]

-- A floor class cannot fill one of the original zero cells.
example {Q : Board 2 3} (h : SameSupportFloor boundaryBoard 1 Q) : Q 1 0 = 0 := by
  exact (h 1 0).1 (by norm_num [boundaryBoard])

example : ¬ SameSupportFloor boundaryBoard (1 / 6) (uniformBoard 2 3) := by
  intro h
  have hz := (h 1 0).1 (by norm_num [boundaryBoard])
  norm_num [uniformBoard] at hz

-- Both equal-support row and column conclusions concern the same Q.
example {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (hmax : IsSeparationGlobalMax P k) (hk : 2 ≤ k) :
    ∃ (ε : ℝ) (Q : Board m n), 0 < ε ∧ IsProbability Q ∧ IsSeparationGlobalMax Q k ∧
      SameSupportFloor P ε Q ∧
      (∀ a b, (∀ i, 0 < P i a ↔ 0 < P i b) → ∀ i, Q i a = Q i b) ∧
      (∀ a b, (∀ j, 0 < P a j ↔ 0 < P b j) → ∀ j, Q a j = Q b j) :=
  exists_same_support_normal_form hP hmax hk

-- The finite floor construction also handles an empty board.
example (P : Board 0 0) : ∃ ε : ℝ, 0 < ε ∧ SameSupportFloor P ε P :=
  exists_sameSupportFloor P

#print axioms DittertRybin.isCompact_supportedMaximizerSet
#print axioms DittertRybin.exists_same_support_normal_form
#print axioms DittertRybin.IsSeparationGlobalMax.value_eq_uniform_of_positive

end DittertRybin.Tests.ThreeRowSupportNormal
