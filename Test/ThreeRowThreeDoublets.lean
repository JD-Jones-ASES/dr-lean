import DR.Rectangular.ThreeRowThreeDoublets

namespace DittertRybin.Tests
open scoped BigOperators

-- A full column makes every remaining row strictly positive, including equal-mass faces.
example {n : ℕ} {P : Board 3 n} (hP : ∀ i j, 0 ≤ P i j)
    (a b c : Fin n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ThreeRowFullColumn P c) (i : Fin 3) :
    0 < threeRowRemainingRow P a b i :=
  threeRowRemainingRow_pos_of_full hP a b hab c hca hcb hc i

-- The zero residual boundary permits equal masses; strict positivity cannot be discarded.
example : (1 : ℝ) ^ 2 + 1 * 1 + 1 ^ 2 - 0 ^ 2 = 3 ∧
    1 * 1 * (2 * (1 + 1 + 0) - 1) = 3 := by norm_num

private noncomputable def threeDoubletsFull : Board 3 4 :=
  fun i j => if i.val = j.val then 0 else 1 / 9

example : IsProbability threeDoubletsFull := by
  constructor
  · intro i j
    dsimp [threeDoubletsFull]
    split <;> norm_num
  · norm_num [totalMass, rowSum, threeDoubletsFull, Fin.sum_univ_succ]

example (i : Fin 3) : ThreeRowDoublet threeDoubletsFull i ⟨i.val, by omega⟩ := by
  fin_cases i <;> norm_num [ThreeRowDoublet, threeDoubletsFull, Fin.add_def]

example : ThreeRowFullColumn threeDoubletsFull 3 := by
  intro i
  fin_cases i <;> norm_num [threeDoubletsFull]

-- This feasible boundary matrix is excluded from actual global maximality.
example : ¬ IsSeparationGlobalMax threeDoubletsFull 3 := by
  intro hmax
  have hP : IsProbability threeDoubletsFull := by
    constructor
    · intro i j
      dsimp [threeDoubletsFull]
      split <;> norm_num
    · norm_num [totalMass, rowSum, threeDoubletsFull, Fin.sum_univ_succ]
  apply hmax.threeRow_not_all_doublet_types hP (by norm_num)
  intro i
  refine ⟨⟨i.val, by omega⟩, ?_⟩
  fin_cases i <;> norm_num [ThreeRowDoublet, threeDoubletsFull, Fin.add_def]

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P)
    (hmax : IsSeparationGlobalMax P 3) (hn : 3 ≤ n) :
    ∃ i, ∀ a, ¬ ThreeRowDoublet P i a := by
  by_contra h
  push Not at h
  exact hmax.threeRow_not_all_doublet_types hP hn h

#print axioms IsSeparationGlobalMax.threeRow_full_pair_majority
#print axioms IsSeparationGlobalMax.threeRow_full_column_offset
#print axioms IsSeparationGlobalMax.threeRow_ordered_three_doublets_impossible
#print axioms IsSeparationGlobalMax.threeRow_not_all_doublet_types
end DittertRybin.Tests
