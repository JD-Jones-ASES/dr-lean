import DR.Rectangular.ThreeRowFinal

namespace DittertRybin.Tests

-- Arbitrary n, with all cells in the closed probability simplex and no auxiliary assumptions.
example {n : ℕ} (hn : 3 ≤ n) : UniformMaximizer 3 n 3 := uniformMaximizer_three_rows hn
example {m : ℕ} (hm : 3 ≤ m) : UniformMaximizer m 3 3 := uniformMaximizer_three_columns hm
example : UniformMaximizer 3 500 3 := uniformMaximizer_three_rows (by norm_num)
example : UniformMaximizer 3 3 3 := uniformMaximizer_three_rows (by norm_num)

example {n : ℕ} (hn : 3 ≤ n) {P : Board 3 n} (hP : IsProbability P) (i : Fin 3) (j : Fin n)
    (hz : P i j = 0) : separationProbability P 3 < uniformSeparationValue 3 n 3 :=
  separationProbability_three_rows_lt_uniform_of_zero hn hP i j hz

private noncomputable def twoColumnBoundary : Board 3 2 :=
  fun _ j => if j.val=0 then 1/3 else 0

private theorem twoColumnBoundary_probability : IsProbability twoColumnBoundary := by
  constructor
  · intro i j
    dsimp [twoColumnBoundary]
    split <;> norm_num
  · norm_num [totalMass, rowSum, twoColumnBoundary, Fin.sum_univ_succ]

private theorem twoColumnBoundary_value : separationProbability twoColumnBoundary 3 = 2/9 := by
  rw [separationProbability_threeRow_cubic]
  norm_num [threeRowSuccessPolynomial, totalMass, rowSum, colSum, twoColumnBoundary, Fin.sum_univ_succ]

-- At n=2 a nonuniform boundary matrix attains the uniform value: the dimension guard is sharp.
example : ¬ UniformMaximizer 3 2 3 := by
  intro h
  have hv : uniformSeparationValue 3 2 3 = 2/9 := by
    norm_num [uniformSeparationValue, distinctUniformProbability]
  have he := (h twoColumnBoundary twoColumnBoundary_probability).2.mp (twoColumnBoundary_value.trans hv.symm)
  have he01 := congrFun (congrFun he (0 : Fin 3)) (1 : Fin 2)
  norm_num [twoColumnBoundary, uniformBoard] at he01

#print axioms IsSeparationGlobalMax.threeRow_positive
#print axioms IsSeparationGlobalMax.threeRow_eq_uniform
#print axioms uniformMaximizer_three_rows
#print axioms uniformMaximizer_three_columns
#print axioms separationProbability_three_rows_lt_uniform_of_zero
end DittertRybin.Tests
