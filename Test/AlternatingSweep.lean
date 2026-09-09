import DR.Square.AlternatingSweep

open scoped BigOperators
open DittertRybin

example (q κ : ℝ) : alternatingBoundary q 0 κ = 0 := by simp [alternatingBoundary]

/-- Division is total in Lean; the strict denominator guard is essential to the theorem. -/
example : alternatingBoundary 1 (2 / 15) (2 / 15) = 0 := by norm_num [alternatingBoundary]
example : ¬(2 / 15 : ℝ) < 1 * (2 / 15) := by norm_num

/-- Reject replacing the proved kappa=2/15 by the larger 1/7. -/
example : (26 / 7 : ℝ) * (∑ j : Fin 5, (![1, 7/4, 2, 7/4, 1] : Fin 5 → ℝ) j ^ 2) <
    ∑ i, joinSix ![1, 7/4, 2, 7/4, 1] i ^ 2 := by
  norm_num [joinSix, Fin.sum_univ_succ]
  dsimp
  norm_num

/-- Paired tied scores have zero alternating energy when the separating weights vanish. -/
example : (∑ j : Fin 11, alternatingWeights 11 1 0 j *
      sweepGap (![0,0,0,0,0,0,1,1,1,1,1,1] : Fin 12 → ℝ) j ^ 2) = 0 := by
  norm_num [alternatingWeights, sweepGap, Fin.sum_univ_succ]

/-- The same score is nonconstant and has positive centered variance. -/
example : (∑ i : Fin 12, ((![0,0,0,0,0,0,1,1,1,1,1,1] : Fin 12 → ℝ) i - 1/2) ^ 2) = 3 := by
  norm_num [Fin.sum_univ_succ]

example : (sweepPrefix (evenPrefixIndexTwelve 0)).card = 2 := evenPrefixIndexTwelve_card 0
example : (sweepPrefix (evenPrefixIndexTwelve 4)).card = 10 := evenPrefixIndexTwelve_card 4

#print axioms DittertRybin.incidence_strict_bound_transfer
#print axioms DittertRybin.alternating_twelve_strict
#print axioms DittertRybin.exists_even_sweep_prefix_twelve
