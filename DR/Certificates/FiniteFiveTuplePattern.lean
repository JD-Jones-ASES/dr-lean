import DR.Certificates.FiniteFiveTuplePatternData

/-! Complete equality-pattern compression for five positions, including
the exact 51-pattern restriction when the tuple has a repeated label. -/

namespace DittertRybin.Certificates

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem fiveTuplePatterns_cover : ∀ p : Fin 5 → Fin 5,
    IsTuplePattern p → ∃ a : Fin 52, fiveTuplePatterns a = p := by
  decide +kernel

theorem fiveTuplePatterns_valid : ∀ a : Fin 52, IsTuplePattern (fiveTuplePatterns a) := by
  decide +kernel

theorem fiveTuplePatterns_complete (p : Fin 5 → Fin 5) :
    IsTuplePattern p ↔ ∃ a : Fin 52, fiveTuplePatterns a = p := by
  constructor
  · exact fiveTuplePatterns_cover p
  · rintro ⟨a, rfl⟩
    exact fiveTuplePatterns_valid a

theorem fiveTuplePatterns_injective : Function.Injective fiveTuplePatterns := by
  decide +kernel

theorem fiveTuplePatterns_last : fiveTuplePatterns 51 = id := by
  decide +kernel

variable {α : Type*} [DecidableEq α]

def fiveTuplePatternIndex (s : Fin 5 → α) : Fin 52 :=
  (Finset.univ.filter fun a => fiveTuplePatterns a = tupleFirstIndex s).min'
    (by
      obtain ⟨a, ha⟩ := (fiveTuplePatterns_complete _).mp (tupleFirstIndex_isPattern s)
      exact ⟨a, by simp [ha]⟩)

theorem fiveTuplePatternIndex_spec (s : Fin 5 → α) :
    fiveTuplePatterns (fiveTuplePatternIndex s) = tupleFirstIndex s := by
  unfold fiveTuplePatternIndex
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter fun a : Fin 52 => fiveTuplePatterns a = tupleFirstIndex s) _)).2

theorem fiveTuplePatternIndex_eq_iff (s : Fin 5 → α) (i j : Fin 5) :
    fiveTuplePatterns (fiveTuplePatternIndex s) i =
      fiveTuplePatterns (fiveTuplePatternIndex s) j ↔ s i = s j := by
  rw [fiveTuplePatternIndex_spec]
  exact tupleFirstIndex_eq_iff s i j

theorem fiveTuplePatternIndex_congr {β : Type*} [DecidableEq β]
    (s : Fin 5 → α) (t : Fin 5 → β) (h : ∀ i j, s i = s j ↔ t i = t j) :
    fiveTuplePatternIndex s = fiveTuplePatternIndex t := by
  apply fiveTuplePatterns_injective
  rw [fiveTuplePatternIndex_spec, fiveTuplePatternIndex_spec]
  exact tupleFirstIndex_congr s t h

theorem fiveTuplePatternIndex_comp (s : Fin 5 → α) (f : Fin 5 → Fin 5) :
    fiveTuplePatternIndex (s ∘ f) =
      fiveTuplePatternIndex (fiveTuplePatterns (fiveTuplePatternIndex s) ∘ f) := by
  apply fiveTuplePatternIndex_congr
  intro i j
  exact (fiveTuplePatternIndex_eq_iff s (f i) (f j)).symm

theorem fiveTuplePatternIndex_pattern (a : Fin 52) :
    fiveTuplePatternIndex (fiveTuplePatterns a) = a := by
  apply fiveTuplePatterns_injective
  rw [fiveTuplePatternIndex_spec]
  exact tupleFirstIndex_pattern ((fiveTuplePatterns_complete _).mpr ⟨a, rfl⟩)

/-- Exactly the last pattern has five distinct labels. -/
theorem fiveTuplePatternIndex_lt_fiftyOne (s : Fin 5 → α) (h : ¬Function.Injective s) :
    (fiveTuplePatternIndex s).val < 51 := by
  by_contra hn
  have he : fiveTuplePatternIndex s = 51 := Fin.ext (by omega)
  apply h
  intro i j hij
  have hp := (fiveTuplePatternIndex_eq_iff s i j).mpr hij
  simpa only [he, fiveTuplePatterns_last, id_eq] using hp

end DittertRybin.Certificates
