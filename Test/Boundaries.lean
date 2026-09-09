import DR
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Regression checks for zero-capacity and zero-support boundary contracts. -/

open DittertRybin

private theorem square_capacity_zero : univariateCapacity (fun t : ℝ => t ^ 2) = 0 := by
  apply le_antisymm
  · apply univariateCapacity_le_deriv_of_zero
    · intro t ht
      positivity
    · norm_num
    · convert! (hasDerivAt_id (0 : ℝ)).pow 2 using 1
      simp
  · exact univariateCapacity_nonneg fun t ht => sq_nonneg t

/-- Equality in the univariate bound can occur at zero capacity with zero roots. -/
example : capacityFactor 2 * univariateCapacity (fun t : ℝ => t ^ 2) =
    deriv (fun t : ℝ => t ^ 2) 0 := by
  rw [square_capacity_zero, mul_zero]
  symm
  convert! ((hasDerivAt_id (0 : ℝ)).pow 2).deriv using 1
  simp

/-- A positive demand cannot cross a zero-capacity one-cell board. -/
example : ¬ ∃ B : Board 1 1, IsTransport 0 1 B := by
  rintro ⟨B, hB⟩
  have h := hB.cuts Finset.univ Finset.univ
  norm_num [cutMass] at h

/-- Zero demand remains feasible even when all capacities vanish. -/
example : ∃ B : Board 2 2, IsTransport 0 0 B :=
  ⟨0, zero_isTransport (by simp)⟩

/-- The documented D4 threshold has its exact intended value. -/
example : largeBoardThreshold 4 = 3659766016 := largeBoardThreshold_four
