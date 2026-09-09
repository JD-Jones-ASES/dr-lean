import DR.Rectangular.ThreeRowSingletonShape

namespace DittertRybin.Tests

-- Zero x is retained: the full-column bound can be attained exactly.
example {u v w : ℝ} (hw : 0 ≤ w) (h : 2 * (u - v) = 2 * w) : v + w ≤ u := by
  exact threeRow_singleton_full_scalar (x := 0) (y := 1) (by norm_num) hw (by norm_num)
    (by nlinarith only [h])

-- The opposite bound is weak at zero residual common-row mass.
example : 0 ≤ ((1 : ℝ) + 0) * 1 - (1 + 4 * 0) * 1 := by norm_num
example : ¬ (0 ≤ ((1 : ℝ) + 1) * 1 - (1 + 4 * 1) * 1) := by norm_num

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) : P i b = 0 ∧ P h b = P i a :=
  hmax.threeRow_symmetric_singleton_opposite_entries hP hn i h k hih hik hhk hsym a ha b hb

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) (c : Fin n) (hcb : c ≠ b) : P h c = 0 :=
  hmax.threeRow_symmetric_singleton_other_zero hP hn i h k hih hik hhk hsym a ha b hb c hcb

-- The representative is an actual probability/global maximum, not a relaxed support matrix.
example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i : Fin 3) (a : Fin n) (ha : ThreeRowSingleton P i a) :
    ∃ (Q : Board 3 n) (b : Fin n) (u : ℝ), IsProbability Q ∧ IsSeparationGlobalMax Q 3 ∧
      0 < u ∧ ∀ r c, Q r c = if r = i then (if c = b then 0 else u) else (if c = b then u else 0) :=
  hmax.threeRow_singleton_global_representative hP hn i a ha

#print axioms IsSeparationGlobalMax.threeRow_symmetric_singleton_opposite_entries
#print axioms IsSeparationGlobalMax.threeRow_symmetric_singleton_shape
#print axioms IsSeparationGlobalMax.threeRow_singleton_global_representative
end DittertRybin.Tests
