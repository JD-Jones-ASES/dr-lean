import DR.Rectangular.FourRowFinal

namespace DittertRybin.Tests

example : UniformMaximizer 4 4 4 := uniformMaximizer_orderFour_four_rows (by decide)
example : UniformMaximizer 4 5 4 := uniformMaximizer_orderFour_four_rows (by decide)

-- Both closed finite intervals include the shared boundary.
example : UniformMaximizer 4 50 4 :=
  uniformMaximizer_orderFour_four_rows_five_fifty (by omega)
example : UniformMaximizer 4 50 4 :=
  uniformMaximizer_orderFour_four_rows_fifty_fiveHundred (by omega)

-- The last finite endpoint and the immediately following analytic dimension.
example : UniformMaximizer 4 500 4 := uniformMaximizer_orderFour_four_rows_finite (by omega)
example : UniformMaximizer 4 501 4 := uniformMaximizer_orderFour_four_rows (by decide)
example : UniformMaximizer 5000 4 4 := uniformMaximizer_orderFour_four_columns (by decide)

-- The release declaration exports both complete orientations together.
example {n : ℕ} (hn : 4 ≤ n) : UniformMaximizer 4 n 4 ∧ UniformMaximizer n 4 4 :=
  uniform_maximum_four_rows hn

-- The smallest nonsquare endpoint has the exact full-simplex value.
example (P : Board 4 5) (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P 4 ≤ (1071/4000 : ℝ) ∧
      (separationProbability P 4 = (1071/4000 : ℝ) ↔ P = uniformBoard 4 5) := by
  have h := fourRow_orderFour_closed_simplex (by decide : 4 ≤ 5) P hP hmass
  norm_num at h
  exact h

-- Decreasing the sharp constant is rejected by the literal uniform board.
example : ¬ separationProbability (uniformBoard 4 5) 4 ≤ (1070/4000 : ℝ) := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue,distinctUniformProbability,Nat.descFactorial]

-- Every boundary zero is strict, with no support or positivity assumption elsewhere.
example {n : ℕ} (hn : 4 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (i : Fin 4) (j : Fin n) (hz : P i j = 0) :
    separationProbability P 4 < uniformSeparationValue 4 n 4 :=
  separationProbability_four_rows_lt_uniform_of_zero hn hP i j hz

#print axioms fourRowFinite5_entry_criterion
#print axioms fourRowFinite50_entry_criterion
#print axioms uniformMaximizer_orderFour_four_rows_finite
#print axioms uniformMaximizer_orderFour_four_rows
#print axioms uniformMaximizer_orderFour_four_columns
#print axioms fourRow_orderFour_closed_simplex
#print axioms separationProbability_four_rows_lt_uniform_of_zero
#print axioms uniform_maximum_four_rows

end DittertRybin.Tests
