import DR.Rectangular.LargeBoards

/-!
Scope checks for the principal rectangular theorems. These deliberately expose
the closed probability simplex and the exact iff equality statement rather than
accepting a theorem about a restricted contender or positive-support class.
-/

open DittertRybin

example {m n k : ℕ} (hk : 4 ≤ k)
    (hm : largeBoardThreshold k ≤ m) (hn : largeBoardThreshold k ≤ n)
    (P : Board m n) (hP : (∀ i j, 0 ≤ P i j) ∧ totalMass P = 1) :
    separationProbability P k ≤ uniformSeparationValue m n k ∧
      (separationProbability P k = uniformSeparationValue m n k ↔
        P = uniformBoard m n) :=
  uniform_maximum_large_boards hk hm hn P hP

example {m n k : ℕ} (hk : 4 ≤ k) (hm : k ^ 21 ≤ m) (hn : k ^ 21 ≤ n)
    (P : Board m n) (hP : (∀ i j, 0 ≤ P i j) ∧ totalMass P = 1) :
    separationProbability P k ≤ uniformSeparationValue m n k ∧
      (separationProbability P k = uniformSeparationValue m n k ↔
        P = uniformBoard m n) :=
  uniform_maximum_large_boards_power hk hm hn P hP

-- The exact threshold endpoint is included independently in both dimensions.
example {n : ℕ} (hn : 3659766016 ≤ n) : UniformMaximizer 3659766016 n 4 := by
  apply uniform_maximum_large_boards (by decide)
  · norm_num [largeBoardThreshold, collisionConstant, Nat.choose]
  · simpa [largeBoardThreshold, collisionConstant, Nat.choose] using hn
