import DR.Rectangular.FourRowFiniteParameter

open DittertRybin
open scoped BigOperators

example : fourRowFiniteParameter 5 5 = 1 := by norm_num [fourRowFiniteParameter]
example : fourRowFiniteParameter 5 50 = 1/10 := by norm_num [fourRowFiniteParameter]
example : fourRowFiniteParameter 50 50 = 1 := by norm_num [fourRowFiniteParameter]
example : fourRowFiniteParameter 50 500 = 1/10 := by norm_num [fourRowFiniteParameter]

example {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 50) :
    0 < fourRowFiniteParameter 5 n * fourRowFiniteDenominator 5 (fourRowFiniteParameter 5 n) :=
  fourRowFiniteClearingFactor_at_columns (by decide) hn.1 (by omega)

example {n : ℕ} (hn : 50 ≤ n ∧ n ≤ 500) :
    0 < fourRowFiniteParameter 50 n * fourRowFiniteDenominator 50 (fourRowFiniteParameter 50 n) :=
  fourRowFiniteClearingFactor_at_columns (by decide) hn.1 (by omega)

example : fourRowFiniteDenominator 5 1 = 24/125 := by
  norm_num [fourRowFiniteDenominator, Fin.prod_univ_succ]

example : fourRowFiniteDenominator 5 1 / (5/1 - (2:ℝ)) = 8/125 := by
  norm_num [fourRowFiniteDenominator, Fin.prod_univ_succ]

/-- The ordinary-column class can have size two at the small endpoint. -/
example : 0 < 5 - ((2 : Fin 3) : ℕ) - 1 := by decide

/-- Positivity does not extend through the first forbidden parameter root. -/
example : ¬ 0 < (5:ℝ) * fourRowFiniteDenominator 5 5 := by
  norm_num [fourRowFiniteDenominator, Fin.prod_univ_succ]

#print axioms fourRowFiniteParameter_coverage
#print axioms fourRowFiniteDenominator_cancel
#print axioms fourRowFiniteParameter_dimension
#print axioms fourRowFiniteClearingFactor_at_columns
#print axioms fourRowFinite_ordinary_count
