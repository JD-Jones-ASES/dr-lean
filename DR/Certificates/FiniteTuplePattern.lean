import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Dimension-independent equality patterns of finite tuples

Replace each tuple entry by the first position with that value. This keeps
exactly all equality relations and uses only the tuple length, regardless of
the ambient label type. For four positions there are fifteen possibilities
on each axis. These labels are first-position labels, not the sequential
first-occurrence ranks used to display the certificate catalogue.
-/

namespace DittertRybin.Certificates

variable {α : Type*} [DecidableEq α] {k : ℕ}

def tupleFirstIndex (s : Fin k → α) (i : Fin k) : Fin k :=
  (Finset.univ.filter fun j => s j = s i).min' ⟨i, by simp⟩

theorem tupleFirstIndex_value (s : Fin k → α) (i : Fin k) :
    s (tupleFirstIndex s i) = s i := by
  have h := Finset.min'_mem (Finset.univ.filter fun j => s j = s i) ⟨i, by simp⟩
  exact (Finset.mem_filter.mp h).2

theorem tupleFirstIndex_le (s : Fin k → α) (i : Fin k) : tupleFirstIndex s i ≤ i :=
  Finset.min'_le _ _ (by simp)

theorem tupleFirstIndex_eq_iff (s : Fin k → α) (i j : Fin k) :
    tupleFirstIndex s i = tupleFirstIndex s j ↔ s i = s j := by
  constructor
  · intro h
    exact (tupleFirstIndex_value s i).symm.trans
      ((congrArg s h).trans (tupleFirstIndex_value s j))
  · intro h
    unfold tupleFirstIndex
    simp only [h]

theorem tupleFirstIndex_idem (s : Fin k → α) (i : Fin k) :
    tupleFirstIndex s (tupleFirstIndex s i) = tupleFirstIndex s i :=
  (tupleFirstIndex_eq_iff s _ i).mpr (tupleFirstIndex_value s i)

/-- First-position representatives are bounded by their position and fix their own image. -/
def IsTuplePattern (p : Fin k → Fin k) : Prop :=
  (∀ i, p i ≤ i) ∧ ∀ i, p (p i) = p i

instance (p : Fin k → Fin k) : Decidable (IsTuplePattern p) := by
  unfold IsTuplePattern
  infer_instance

theorem tupleFirstIndex_isPattern (s : Fin k → α) : IsTuplePattern (tupleFirstIndex s) :=
  ⟨tupleFirstIndex_le s, tupleFirstIndex_idem s⟩

/-- Every admitted representative pattern is itself its literal first-index compression. -/
theorem tupleFirstIndex_pattern {p : Fin k → Fin k} (hp : IsTuplePattern p) :
    tupleFirstIndex p = p := by
  funext i
  apply le_antisymm
  · apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp.2 i
  · have h := tupleFirstIndex_value p i
    rw [← h]
    exact hp.1 _

/-- The complete fifteen first-position patterns of four labels. -/
def fourTuplePatterns : Fin 15 → (Fin 4 → Fin 4) :=
  ![![0,0,0,0], ![0,0,0,3], ![0,0,2,0], ![0,0,2,2], ![0,0,2,3],
    ![0,1,0,0], ![0,1,0,1], ![0,1,0,3], ![0,1,1,0], ![0,1,1,1],
    ![0,1,1,3], ![0,1,2,0], ![0,1,2,1], ![0,1,2,2], ![0,1,2,3]]

theorem fourTuplePatterns_complete : ∀ p : Fin 4 → Fin 4,
    IsTuplePattern p ↔ ∃ a : Fin 15, fourTuplePatterns a = p := by
  decide +kernel

theorem fourTuplePatterns_injective : Function.Injective fourTuplePatterns := by
  decide +kernel

/-- Every tuple in any ambient type has one of the fifteen literal equality patterns. -/
theorem exists_fourTuplePattern (s : Fin 4 → α) :
    ∃ a : Fin 15, ∀ i j, s i = s j ↔ fourTuplePatterns a i = fourTuplePatterns a j := by
  obtain ⟨a,ha⟩ := (fourTuplePatterns_complete (tupleFirstIndex s)).mp (tupleFirstIndex_isPattern s)
  refine ⟨a, ?_⟩
  intro i j
  rw [ha]
  exact (tupleFirstIndex_eq_iff s i j).symm

theorem tupleFirstIndex_congr {β : Type*} [DecidableEq β]
    (s : Fin k → α) (t : Fin k → β) (h : ∀ i j, s i = s j ↔ t i = t j) :
    tupleFirstIndex s = tupleFirstIndex t := by
  funext i
  unfold tupleFirstIndex
  simp_rw [h]

/-- A computable index in the complete four-position catalogue. -/
def fourTuplePatternIndex (s : Fin 4 → α) : Fin 15 :=
  (Finset.univ.filter fun a => fourTuplePatterns a = tupleFirstIndex s).min'
    (by
      obtain ⟨a,ha⟩ := (fourTuplePatterns_complete _).mp (tupleFirstIndex_isPattern s)
      exact ⟨a, by simp [ha]⟩)

theorem fourTuplePatternIndex_spec (s : Fin 4 → α) :
    fourTuplePatterns (fourTuplePatternIndex s) = tupleFirstIndex s := by
  unfold fourTuplePatternIndex
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter fun a : Fin 15 => fourTuplePatterns a = tupleFirstIndex s) _)).2

theorem fourTuplePatternIndex_eq_iff (s : Fin 4 → α) (i j : Fin 4) :
    fourTuplePatterns (fourTuplePatternIndex s) i =
      fourTuplePatterns (fourTuplePatternIndex s) j ↔ s i = s j := by
  rw [fourTuplePatternIndex_spec]
  exact tupleFirstIndex_eq_iff s i j

theorem fourTuplePatternIndex_congr {β : Type*} [DecidableEq β]
    (s : Fin 4 → α) (t : Fin 4 → β) (h : ∀ i j, s i = s j ↔ t i = t j) :
    fourTuplePatternIndex s = fourTuplePatternIndex t := by
  apply fourTuplePatterns_injective
  rw [fourTuplePatternIndex_spec, fourTuplePatternIndex_spec]
  exact tupleFirstIndex_congr s t h

/-- Tuple-position substitution is computed entirely inside the fixed catalogue. -/
theorem fourTuplePatternIndex_comp (s : Fin 4 → α) (f : Fin 4 → Fin 4) :
    fourTuplePatternIndex (s ∘ f) =
      fourTuplePatternIndex (fourTuplePatterns (fourTuplePatternIndex s) ∘ f) := by
  apply fourTuplePatternIndex_congr
  intro i j
  exact (fourTuplePatternIndex_eq_iff s (f i) (f j)).symm

theorem fourTuplePatternIndex_pattern (a : Fin 15) :
    fourTuplePatternIndex (fourTuplePatterns a) = a := by
  apply fourTuplePatterns_injective
  rw [fourTuplePatternIndex_spec]
  exact tupleFirstIndex_pattern ((fourTuplePatterns_complete _).mpr ⟨a,rfl⟩)

end DittertRybin.Certificates
