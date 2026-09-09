import DR
import Mathlib.Tactic.NormNum

/-! Small semantic controls for normalization, empty draws and oversampling. -/

open DittertRybin

example : separationProbability (uniformBoard 2 3) 0 = 1 := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue, distinctUniformProbability]

example : separationProbability (uniformBoard 2 3) 4 = 0 := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

example : separationProbability (uniformBoard 3 4) 3 = 37 / 72 := by
  rw [separationProbability_uniform (by decide) (by decide)]
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

example {m n : ℕ} {P : Board m n} (hP : IsProbability P) :
    separationProbability P 1 = 1 := separationProbability_one hP

example : UniformMaximizer 3 7 2 := uniform_maximum_order_two (by decide) (by decide)

example : DittertMaximizer 2 := dittert_order_two
