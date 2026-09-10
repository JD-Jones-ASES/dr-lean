import DR.Rectangular.FiveByFiveFinal

namespace DittertRybin.Tests

-- All four admissible nontrivial orders use the exact full-simplex statement.
example {k : ℕ} (hk : 2≤k) (hk5 : k≤5) (P : Board 5 5) (hP : IsProbability P) :
    separationProbability P k ≤ uniformSeparationValue 5 5 k ∧
    (separationProbability P k=uniformSeparationValue 5 5 k ↔ P=uniformBoard 5 5) :=
  uniform_maximum_five_by_five hk hk5 P hP

example : UniformMaximizer 5 5 2 ∧ UniformMaximizer 5 5 3 ∧
    UniformMaximizer 5 5 4 ∧ UniformMaximizer 5 5 5 :=
  ⟨uniform_maximum_five_by_five (by decide) (by decide),
    uniform_maximum_five_by_five (by decide) (by decide),
    uniform_maximum_five_by_five (by decide) (by decide),
    uniform_maximum_five_by_five (by decide) (by decide)⟩

example {k : ℕ} (hk : 2≤k) (hk5 : k≤5) (P : Board 5 5) (hP : IsProbability P)
    (i j : Fin 5) (hz : P i j=0) :
    separationProbability P k < uniformSeparationValue 5 5 k := by
  obtain ⟨hle,heq⟩ := uniform_maximum_five_by_five hk hk5 P hP
  apply lt_of_le_of_ne hle
  intro hv
  rw [heq.mp hv] at hz
  norm_num [uniformBoard] at hz

example {k : ℕ} (hk : 2≤k) (hk5 : k≤5) :
    separationProbability (uniformBoard 5 5) k=uniformSeparationValue 5 5 k :=
  (uniform_maximum_five_by_five hk hk5 _
    (uniformBoard_isProbability (by decide) (by decide))).2.mpr rfl

#print axioms uniform_maximum_five_by_five
end DittertRybin.Tests
