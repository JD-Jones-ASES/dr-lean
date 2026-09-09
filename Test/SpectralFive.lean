import DR.Square.SpectralFive

/-! Final order-five type, normalization, and closed-boundary regression checks. -/

namespace DittertRybin.Tests

open scoped BigOperators

-- The theorem has only nonnegativity and total mass as matrix premises.
example (A : Board 5 5) (hA : ∀ i j, 0 ≤ A i j) (hm : totalMass A = 5) :
    dittertFunctional A ≤ 1226/625 ∧
      (dittertFunctional A = 1226/625 ↔ A = uniformDittertMatrix 5) := by
  have h := dittert_order_five A hA hm
  norm_num [dittertConstant,Nat.factorial] at h
  exact h

example (P : Board 5 5) (hP : IsProbability P) :
    separationProbability P 5 ≤ 29424/390625 ∧
      (separationProbability P 5 = 29424/390625 ↔ P = uniformBoard 5 5) := by
  have h := uniformMaximizer_five_five_five P hP
  rw [uniformSeparationValue_endpoint] at h
  norm_num [dittertConstant,Nat.factorial] at h
  exact h

-- Diagonal matrices, with all off-diagonal cells zero, are in the theorem's domain.
example : dittertFunctional (1 : Board 5 5) ≤ 1226/625 := by
  have hn : ∀ i j, 0 ≤ (1 : Board 5 5) i j := by
    intro i j
    simp only [Matrix.one_apply]
    split <;> norm_num
  have hm : totalMass (1 : Board 5 5) = 5 := by
    simp [totalMass,rowSum,Matrix.one_apply]
  have h := (dittert_order_five (1 : Board 5 5) hn hm).1
  norm_num [dittertConstant,Nat.factorial] at h
  exact h

-- The extremal-coordinate map includes the collapsed zero-deficit face.
example : fiveDeficitParameter 0 = 0 := by simp [fiveDeficitParameter]

#print axioms five_globalMax_singleton_coordinates
#print axioms five_globalMax_singleton_cut_contradiction
#print axioms dittert_globalMax_uniform_five
#print axioms dittert_order_five
#print axioms uniformMaximizer_five_five_five

end DittertRybin.Tests
