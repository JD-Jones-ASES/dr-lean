import DR.Semimatching
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The exact uniform semimatching probability

An ordered sample with distinct rows consists of a row injection and an
arbitrary column function. Requiring distinct columns as well replaces that
function by a second injection. These explicit equivalences reduce all three
counts in inclusion-exclusion to descending factorials.

The formula holds for every sample size, including zero and sizes exceeding
one or both dimensions. Only positivity of the board dimensions is required.
-/

namespace DittertRybin

open scoped BigOperators

/-- Separate a row-distinct cell sample into its row injection and column function. -/
def rowsDistinctEquiv (m n k : ℕ) :
    {s : Fin k → Fin m × Fin n // RowsDistinct s} ≃
      (Fin k ↪ Fin m) × (Fin k → Fin n) where
  toFun s := (⟨fun t => (s.val t).1, s.property⟩, fun t => (s.val t).2)
  invFun f := ⟨fun t => (f.1 t, f.2 t), f.1.injective⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv f := by
    rcases f with ⟨⟨f, hf⟩, g⟩
    rfl

/-- Separate a column-distinct cell sample into its row function and column injection. -/
def colsDistinctEquiv (m n k : ℕ) :
    {s : Fin k → Fin m × Fin n // ColsDistinct s} ≃
      (Fin k → Fin m) × (Fin k ↪ Fin n) where
  toFun s := (fun t => (s.val t).1, ⟨fun t => (s.val t).2, s.property⟩)
  invFun f := ⟨fun t => (f.1 t, f.2 t), f.2.injective⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv f := by
    rcases f with ⟨f, ⟨g, hg⟩⟩
    rfl

/-- Samples with distinct rows and columns are exactly pairs of injections. -/
def rowsColsDistinctEquiv (m n k : ℕ) :
    {s : Fin k → Fin m × Fin n // RowsDistinct s ∧ ColsDistinct s} ≃
      (Fin k ↪ Fin m) × (Fin k ↪ Fin n) where
  toFun s := (⟨fun t => (s.val t).1, s.property.1⟩,
    ⟨fun t => (s.val t).2, s.property.2⟩)
  invFun f := ⟨fun t => (f.1 t, f.2 t), f.1.injective, f.2.injective⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv f := by
    rcases f with ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    rfl

theorem card_rowsDistinct (m n k : ℕ) :
    Nat.card {s : Fin k → Fin m × Fin n // RowsDistinct s} =
      m.descFactorial k * n ^ k := by
  classical
  rw [Nat.card_congr (rowsDistinctEquiv m n k)]
  simp [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

theorem card_colsDistinct (m n k : ℕ) :
    Nat.card {s : Fin k → Fin m × Fin n // ColsDistinct s} =
      m ^ k * n.descFactorial k := by
  classical
  rw [Nat.card_congr (colsDistinctEquiv m n k)]
  simp [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

theorem card_rowsColsDistinct (m n k : ℕ) :
    Nat.card {s : Fin k → Fin m × Fin n // RowsDistinct s ∧ ColsDistinct s} =
      m.descFactorial k * n.descFactorial k := by
  classical
  rw [Nat.card_congr (rowsColsDistinctEquiv m n k)]
  simp [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

/-- Under constant cell weights, event mass is the number of samples times their common weight. -/
theorem eventMass_const {α : Type*} [Fintype α] {k : ℕ}
    (q : ℝ) (E : Set (Fin k → α)) :
    eventMass (fun _ : α => q) E = (Nat.card E : ℝ) * q ^ k := by
  classical
  simp only [eventMass, sampleMass, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem eventMass_uniform_rows {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    eventMass (fun a : Fin m × Fin n => uniformBoard m n a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s} =
        distinctUniformProbability m k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [uniformBoard]
  rw [eventMass_const]
  change (Nat.card {s : Fin k → Fin m × Fin n // RowsDistinct s} : ℝ) *
    ((m : ℝ) * n)⁻¹ ^ k = _
  rw [card_rowsDistinct m n k]
  simp only [distinctUniformProbability, Nat.cast_mul, Nat.cast_pow, mul_pow, inv_pow]
  field_simp

theorem eventMass_uniform_cols {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    eventMass (fun a : Fin m × Fin n => uniformBoard m n a.1 a.2)
      {s : Fin k → Fin m × Fin n | ColsDistinct s} =
        distinctUniformProbability n k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [uniformBoard]
  rw [eventMass_const]
  change (Nat.card {s : Fin k → Fin m × Fin n // ColsDistinct s} : ℝ) *
    ((m : ℝ) * n)⁻¹ ^ k = _
  rw [card_colsDistinct m n k]
  simp only [distinctUniformProbability, Nat.cast_mul, Nat.cast_pow, mul_pow, inv_pow]
  field_simp

theorem eventMass_uniform_rows_cols {m n k : ℕ} :
    eventMass (fun a : Fin m × Fin n => uniformBoard m n a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s} =
        distinctUniformProbability m k * distinctUniformProbability n k := by
  simp only [uniformBoard]
  rw [eventMass_const]
  change (Nat.card {s : Fin k → Fin m × Fin n // RowsDistinct s ∧ ColsDistinct s} : ℝ) *
    ((m : ℝ) * n)⁻¹ ^ k = _
  rw [card_rowsColsDistinct m n k]
  simp only [distinctUniformProbability, Nat.cast_mul, mul_pow, inv_pow]
  ring

/-- The exact inclusive-OR probability on the uniform board, for every sample size. -/
theorem separationProbability_uniform {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    separationProbability (uniformBoard m n) k = uniformSeparationValue m n k := by
  change eventMass _
    ({s | RowsDistinct s} ∪ {s | ColsDistinct s}) = _
  rw [eventMass_union]
  change _ + _ - eventMass _ {s | RowsDistinct s ∧ ColsDistinct s} = _
  rw [eventMass_uniform_rows hm hn, eventMass_uniform_cols hm hn,
    eventMass_uniform_rows_cols]
  rfl

end DittertRybin
