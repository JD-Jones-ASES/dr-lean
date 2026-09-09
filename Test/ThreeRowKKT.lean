import DR.Rectangular.ThreeRowAveraging

namespace DittertRybin.Tests.ThreeRowKKT
open scoped BigOperators

-- Three occurrences of the same cell contribute three derivative terms.
example : sampleMassGradient (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 3 => (0 : Fin 1)) 0 = 12 := by
  norm_num [sampleMassGradient, Fin.sum_univ_succ, Finset.prod_erase, sampleMass]

-- A missing cell can have a strictly positive derivative. It must remain in KKT.
private theorem erase_zero_three : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide

private def missingCellWeights : Fin 3 → ℝ := ![0, 2, 3]
private theorem missing_derivative : sampleMassGradient missingCellWeights (id : Fin 3 → Fin 3) 0 = 6 := by
  norm_num [sampleMassGradient, missingCellWeights, Fin.sum_univ_succ, erase_zero_three]
  rw [Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2)]
  change (2 : ℝ) * 3 = 6
  norm_num

example : sampleMassGradient missingCellWeights (id : Fin 3 → Fin 3) 0 = 6 := missing_derivative

-- Deleting that derivative because its cell weight is zero is an invalid mutation.
example : ¬ sampleMassGradient missingCellWeights (id : Fin 3 → Fin 3) 0 = 0 := by
  rw [missing_derivative]
  norm_num

-- Empty samples have zero derivative, without a positivity or normalization premise.
example (p : Fin 2 → ℝ) (a : Fin 2) (s : Fin 0 → Fin 2) : sampleMassGradient p s a = 0 := by
  simp [sampleMassGradient]

example {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (hmax : IsSeparationGlobalMax P k) (u : Fin m × Fin n) (hz : P u.1 u.2 = 0) :
    P u.1 u.2 = 0 ∧ separationGradient P k u.1 u.2 ≤ (k : ℝ) * separationProbability P k := by
  exact ⟨hz, hmax.gradient_le_value hP u⟩

-- The algebraic flatness theorem is valid for every parameter, not only the midpoint.
example {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (hmax : IsSeparationGlobalMax P k) (hk : 2 ≤ k) (a b : Fin n) (hab : a ≠ b)
    (hs : ∀ i, 0 < P i a ↔ 0 < P i b) :
    separationProbability (blendColumns P a b (1 / 2)) k = separationProbability P k :=
  hmax.same_support_blend_flat hP hk a b hab hs (1 / 2)

#print axioms DittertRybin.hasDerivAt_separationProbability_line
#print axioms DittertRybin.IsSeparationGlobalMax.gradient_le_value
#print axioms DittertRybin.IsSeparationGlobalMax.same_support_blend_flat

end DittertRybin.Tests.ThreeRowKKT
