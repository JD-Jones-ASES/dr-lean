import DR.Square.AlternatingSweepTen

open scoped BigOperators
open DittertRybin

example : alternatingBoundary 1 0 (19 / 100) = 0 := by simp [alternatingBoundary]

/-- Reject the larger kappa=1/5: its required join bound is false. -/
example : (18 / 5 : ℝ) * (∑ j : Fin 4, (![1, 8/5, 8/5, 1] : Fin 4 → ℝ) j ^ 2) <
    ∑ i, joinFive ![1, 8/5, 8/5, 1] i ^ 2 := by
  norm_num [joinFive, Fin.sum_univ_succ]
  dsimp
  norm_num

/-- Nonconstant paired tied scores retain zero energy when all even-edge weights vanish. -/
example : (∑ j : Fin 9, alternatingWeights 9 1 0 j *
      sweepGap (![0,0,0,0,1,1,1,1,1,1] : Fin 10 → ℝ) j ^ 2) = 0 := by
  norm_num [alternatingWeights, sweepGap, Fin.sum_univ_succ]

example : (∑ i : Fin 10, ((![0,0,0,0,1,1,1,1,1,1] : Fin 10 → ℝ) i - 3/5) ^ 2) = 12/5 := by
  norm_num [Fin.sum_univ_succ]

example : (sweepPrefix (evenPrefixIndexTen 0)).card = 2 := evenPrefixIndexTen_card 0
example : (sweepPrefix (evenPrefixIndexTen 3)).card = 8 := evenPrefixIndexTen_card 3

#print axioms DittertRybin.alternating_ten_strict
#print axioms DittertRybin.exists_even_sweep_prefix_ten
