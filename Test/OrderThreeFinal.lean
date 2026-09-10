import DR.Rectangular.OrderThreeFinal

namespace DittertRybin.Tests
open scoped BigOperators

-- Every finite/infinite transition, the two separate four-row seeds, and
-- the start of the dimension-independent large range reach the final theorem.
example (m n : ℕ) (h : (m,n) ∈
    ([(3,3),(3,960),(4,4),(4,5),(4,6),(4,959),(4,960),
      (5,5),(5,120),(5,121),(6,6),(6,237),(6,238),
      (7,7),(7,24),(7,25),(8,8),(8,14),(8,15),
      (9,9),(9,11),(9,12),(10,10),(10,1000)] : List (ℕ×ℕ))) :
    UniformMaximizer m n 3 ∧ UniformMaximizer n m 3 := by
  have hd : 3 ≤ m ∧ 3 ≤ n := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h <;> obtain ⟨rfl,rfl⟩ := h <;> norm_num
  exact ⟨uniform_maximum_order_three hd.1 hd.2,uniform_maximum_order_three hd.2 hd.1⟩

-- No positivity or balance is added to the closed probability simplex.
example {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (P : Board m n)
    (hP : IsProbability P) :
    separationProbability P 3 ≤ uniformSeparationValue m n 3 ∧
      (separationProbability P 3 = uniformSeparationValue m n 3 ↔ P=uniformBoard m n) :=
  uniform_maximum_order_three hm hn P hP

-- Every genuine boundary zero gives a strict gap, in either orientation.
example {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (P : Board m n)
    (hP : IsProbability P) (i : Fin m) (j : Fin n) (hz : P i j=0) :
    separationProbability P 3 < uniformSeparationValue m n 3 := by
  obtain ⟨hle,heq⟩ := uniform_maximum_order_three hm hn P hP
  apply lt_of_le_of_ne hle
  intro hv
  have hu := heq.mp hv
  rw [hu] at hz
  have hp : (0:ℝ)<uniformBoard m n i j := by
    have hmR : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
    have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    exact inv_pos.mpr (mul_pos hmR hnR)
  rw [hz] at hp
  exact (lt_irrefl 0) hp

-- The finite high endpoint and the tail's first board really attain their
-- respective sharp values; a strict uniform upper bound is impossible.
example : separationProbability (uniformBoard 4 959) 3 = uniformSeparationValue 4 959 3 ∧
    separationProbability (uniformBoard 4 960) 3 = uniformSeparationValue 4 960 3 := by
  exact ⟨(uniform_maximum_order_three (by decide) (by decide) _
    (uniformBoard_isProbability (by decide) (by decide))).2.mpr rfl,
    (uniform_maximum_order_three (by decide) (by decide) _
    (uniformBoard_isProbability (by decide) (by decide))).2.mpr rfl⟩

example : ¬ separationProbability (uniformBoard 9 11) 3 < uniformSeparationValue 9 11 3 := by
  have h := (uniform_maximum_order_three (by decide) (by decide) _
    (uniformBoard_isProbability (m := 9) (n := 11) (by decide) (by decide))).2.mpr rfl
  rw [h]
  exact lt_irrefl _

#print axioms uniformMaximizer_orderThree_finite_4
#print axioms uniformMaximizer_orderThree_finite_5
#print axioms uniformMaximizer_orderThree_finite_6
#print axioms uniformMaximizer_orderThree_finite_7
#print axioms uniformMaximizer_orderThree_finite_8
#print axioms uniformMaximizer_orderThree_finite_9
#print axioms uniform_maximum_order_three
end DittertRybin.Tests
