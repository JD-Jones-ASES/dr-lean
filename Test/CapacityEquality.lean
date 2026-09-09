import DR.Square.CapacityEquality
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Closed-simplex controls for the entropy factor used in permanent equality. -/

open DittertRybin

-- A unit column entry creates a 0^0 factor, which is exactly one.
example : matrixEntropyFactor ![1, 0] = 1 := by
  norm_num [matrixEntropyFactor, Real.rpow_eq_pow, Fin.prod_univ_two]

-- That boundary vector strictly exceeds G(2); it is not an equality case.
example : capacityFactor 2 < matrixEntropyFactor ![1, 0] := by
  norm_num [matrixEntropyFactor, Real.rpow_eq_pow, Fin.prod_univ_two, capacityFactor]

-- The uniform vector attains the factor, with exact rational coordinates.
example : matrixEntropyFactor ![1 / 2, 1 / 2] = capacityFactor 2 := by
  apply le_antisymm
  · apply (matrixEntropyFactor_le_iff (by decide) _
      (by intro i; fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])).mpr
    intro i
    fin_cases i <;> norm_num
  · exact matrixEntropyFactor_lower_bound (by decide) _
      (by intro i; fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])

#print axioms DittertRybin.vanDerWaerden_with_equality
