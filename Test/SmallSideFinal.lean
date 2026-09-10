import DR.Rectangular.SmallSideFinal
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests

-- Every admissible order on each small side, with a large opposite side.
example (k : ℕ) (hk : 2≤k) (hk4 : k≤4) :
    UniformMaximizer 4 1000 k ∧ UniformMaximizer 1000 4 k :=
  ⟨uniform_maximum_small_side (by norm_num) hk (by omega),
    uniform_maximum_small_side (by norm_num) hk (by omega)⟩

example : UniformMaximizer 2 1000 2 ∧ UniformMaximizer 1000 2 2 ∧
    UniformMaximizer 3 1000 3 ∧ UniformMaximizer 1000 3 3 := by
  exact ⟨uniform_maximum_small_side (by norm_num) (by decide) (by decide),
    uniform_maximum_small_side (by norm_num) (by decide) (by decide),
    uniform_maximum_small_side (by norm_num) (by decide) (by decide),
    uniform_maximum_small_side (by norm_num) (by decide) (by decide)⟩

example {m n k : ℕ} (hs : min m n≤4) (hk : 2≤k) (hkmn : k≤min m n)
    (P : Board m n) (hP : IsProbability P) :
    separationProbability P k ≤ uniformSeparationValue m n k ∧
    (separationProbability P k = uniformSeparationValue m n k ↔ P=uniformBoard m n) :=
  uniform_maximum_small_side hs hk hkmn P hP

private noncomputable def concentratedTwo : Board 2 2 := !![1,0;0,0]

private theorem concentrated_probability : IsProbability concentratedTwo := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [concentratedTwo]
  · norm_num [totalMass,rowSum,concentratedTwo,Fin.sum_univ_succ]

-- K=1 cannot be admitted into the uniform-uniqueness declaration.
example : separationProbability concentratedTwo 1=1 ∧ ¬UniformMaximizer 2 2 1 := by
  refine ⟨separationProbability_one concentrated_probability,?_⟩
  intro h
  have heq := (h _ concentrated_probability).2
  have hv : separationProbability concentratedTwo 1=uniformSeparationValue 2 2 1 := by
    rw [separationProbability_one concentrated_probability]
    norm_num [uniformSeparationValue,distinctUniformProbability,Nat.descFactorial]
  have hu := heq.mp hv
  have hcell := congrArg (fun P : Board 2 2 => P 0 0) hu
  norm_num [concentratedTwo,uniformBoard] at hcell

-- The same actual zero-supported matrix receives the nontrivial K=2 strict gap.
example : separationProbability concentratedTwo 2 < uniformSeparationValue 2 2 2 := by
  obtain ⟨hle,heq⟩ := uniform_maximum_small_side (m := 2) (n := 2) (k := 2)
    (by norm_num) (by decide) (by decide) _ concentrated_probability
  apply lt_of_le_of_ne hle
  intro hv
  have hu := heq.mp hv
  have hcell := congrArg (fun P : Board 2 2 => P 0 0) hu
  norm_num [concentratedTwo,uniformBoard] at hcell

#print axioms uniform_maximum_small_side
end DittertRybin.Tests
