import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite independent sampling

A sample is an ordered function `Fin k → α`. Its weight is the product of
the weights of its entries. Consequently, repeated entries are allowed:
this is sampling with replacement.

`eventMass` sums these weights over an event. Its algebraic identities need
no normalization or positivity assumptions; the probability bounds state
those assumptions explicitly. In particular, union means inclusive OR.
-/

namespace DittertRybin

open scoped BigOperators

variable {α : Type*} [Fintype α] {k : ℕ}

/-- Weight of an ordered independent sample, allowing repeated outcomes. -/
def sampleMass (p : α → ℝ) (s : Fin k → α) : ℝ :=
  ∏ t, p (s t)

/-- Total sample weight of an event. For a probability vector this is its probability. -/
noncomputable def eventMass (p : α → ℝ) (E : Set (Fin k → α)) : ℝ := by
  classical
  exact ∑ s, if s ∈ E then sampleMass p s else 0

omit [Fintype α] in
theorem sampleMass_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (s : Fin k → α) : 0 ≤ sampleMass p s := by
  exact Finset.prod_nonneg fun t _ => hp (s t)

/-- Expanding a power gives the total weight of all ordered samples. -/
theorem sum_sampleMass (p : α → ℝ) :
    (∑ s : Fin k → α, sampleMass p s) = (∑ a, p a) ^ k := by
  exact (Fintype.sum_pow p k).symm

/-- Independent sampling preserves normalization, including the empty sample. -/
theorem sum_sampleMass_eq_one (p : α → ℝ) (hp : ∑ a, p a = 1) :
    (∑ s : Fin k → α, sampleMass p s) = 1 := by
  rw [sum_sampleMass, hp, one_pow]

omit [Fintype α] in
@[simp] theorem sampleMass_zero (p : α → ℝ) (s : Fin 0 → α) :
    sampleMass p s = 1 := by
  simp [sampleMass]

@[simp] theorem eventMass_empty (p : α → ℝ) :
    eventMass p (∅ : Set (Fin k → α)) = 0 := by
  classical
  simp [eventMass]

@[simp] theorem eventMass_univ (p : α → ℝ) :
    eventMass p (Set.univ : Set (Fin k → α)) = (∑ a, p a) ^ k := by
  classical
  simpa [eventMass] using sum_sampleMass (k := k) p

theorem eventMass_univ_eq_one (p : α → ℝ) (hp : ∑ a, p a = 1) :
    eventMass p (Set.univ : Set (Fin k → α)) = 1 := by
  rw [eventMass_univ, hp, one_pow]

theorem eventMass_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (E : Set (Fin k → α)) : 0 ≤ eventMass p E := by
  classical
  exact Finset.sum_nonneg fun s _ => by
    by_cases hs : s ∈ E
    · simpa [hs] using sampleMass_nonneg p hp s
    · simp [hs]

/-- The two-event inclusion-exclusion identity before subtraction. -/
theorem eventMass_union_add_inter (p : α → ℝ) (E F : Set (Fin k → α)) :
    eventMass p (E ∪ F) + eventMass p (E ∩ F) =
      eventMass p E + eventMass p F := by
  classical
  simp only [eventMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hE : s ∈ E <;> by_cases hF : s ∈ F <;> simp [hE, hF]

/-- Inclusive OR adds the two event masses and subtracts their overlap. -/
theorem eventMass_union (p : α → ℝ) (E F : Set (Fin k → α)) :
    eventMass p (E ∪ F) = eventMass p E + eventMass p F - eventMass p (E ∩ F) := by
  have h := eventMass_union_add_inter p E F
  exact eq_sub_iff_add_eq.mpr h

theorem eventMass_add_compl (p : α → ℝ) (E : Set (Fin k → α)) :
    eventMass p E + eventMass p Eᶜ = (∑ a, p a) ^ k := by
  have h := eventMass_union_add_inter p E Eᶜ
  simpa using h.symm

theorem eventMass_compl (p : α → ℝ) (hp : ∑ a, p a = 1)
    (E : Set (Fin k → α)) : eventMass p Eᶜ = 1 - eventMass p E := by
  have h := eventMass_add_compl p E
  rw [hp, one_pow] at h
  exact eq_sub_iff_add_eq'.mpr h

theorem eventMass_mono (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    {E F : Set (Fin k → α)} (hEF : E ⊆ F) : eventMass p E ≤ eventMass p F := by
  classical
  apply Finset.sum_le_sum
  intro s _
  by_cases hE : s ∈ E
  · simp [hE, hEF hE]
  · by_cases hF : s ∈ F
    · simpa [hE, hF] using sampleMass_nonneg p hp s
    · simp [hE, hF]

theorem eventMass_le_one (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (E : Set (Fin k → α)) : eventMass p E ≤ 1 := by
  calc
    eventMass p E ≤ eventMass p Set.univ := eventMass_mono p hp (Set.subset_univ E)
    _ = 1 := eventMass_univ_eq_one p hsum

end DittertRybin
