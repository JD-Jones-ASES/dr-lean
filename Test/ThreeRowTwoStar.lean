import DR.Rectangular.ThreeRowTwoStar

namespace DittertRybin.Tests

-- The polynomial calculation retains signed weights before probability normalization.
example : separationProbability (threeRowTwoStar (0 : Fin 3) (0 : Fin 3) (-1)) 3 = -24 := by
  norm_num [separationProbability_threeRowTwoStar]

example : separationProbability (threeRowTwoStar (2 : Fin 3) (1 : Fin 3) (1/4)) 3 = 3/8 := by
  norm_num [separationProbability_threeRowTwoStar]

example : uniformSeparationValue 3 3 3 -
    separationProbability (threeRowTwoStar (1 : Fin 3) (2 : Fin 3) (1/4)) 3 = 13/648 := by
  rw [threeRowTwoStar_uniform_gap (by decide)]
  · norm_num
  · norm_num [totalMass_threeRowTwoStar]

-- At two columns, this nonuniform support has the uniform value. Strictness
-- must therefore retain the n>=3 hypothesis.
example : separationProbability (threeRowTwoStar (0 : Fin 3) (0 : Fin 2) (1/3)) 3 =
    uniformSeparationValue 3 2 3 := by
  rw [separationProbability_threeRowTwoStar, uniformSeparationValue_three_rows (by decide)]
  norm_num

example : threeRowTwoStar (0 : Fin 3) (0 : Fin 2) (1/3) ≠ uniformBoard 3 2 := by
  intro h
  have he := congrArg (fun P : Board 3 2 => P 0 0) h
  norm_num [threeRowTwoStar, uniformBoard] at he

example {n : ℕ} (hn : 3 ≤ n) (i : Fin 3) (b : Fin n) (u : ℝ)
    (hmass : totalMass (threeRowTwoStar i b u) = 1) :
    separationProbability (threeRowTwoStar i b u) 3 <
      separationProbability (uniformBoard 3 n) 3 := by
  rw [separationProbability_uniform (by decide) (by omega)]
  exact separationProbability_threeRowTwoStar_lt_uniform hn i b u hmass

#print axioms separationProbability_threeRowTwoStar
#print axioms threeRowTwoStar_uniform_gap
#print axioms separationProbability_threeRowTwoStar_lt_uniform
end DittertRybin.Tests
