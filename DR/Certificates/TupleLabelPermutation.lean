import DR.Certificates.FiniteTuplePattern
import Mathlib.Logic.Equiv.Fintype

/-!
# Extending equality-preserving tuple relabelings

For a finite tuple of natural labels, an equality-preserving relabeling is
the restriction of a permutation of all natural labels. Repeated entries
and unused labels need no additional hypotheses. This connects finite
equality-pattern tables to formulas invariant under injective relabeling.
-/

namespace DittertRybin.Certificates

/-- Equal equality relations suffice to extend a finite tuple relabeling. -/
theorem tupleLabelPermutation {k : ℕ} (s t : Fin k → ℕ)
    (h : ∀ i j, s i = s j ↔ t i = t j) :
    ∃ σ : Equiv.Perm ℕ, ∀ i, σ (s i) = t i := by
  classical
  let R := {i : Fin k // tupleFirstIndex s i = i}
  have hs : Function.Injective (fun i : R => s i.val) := by
    intro i j hij
    apply Subtype.ext
    have hp := (tupleFirstIndex_eq_iff s i.val j.val).mpr hij
    simpa only [i.property, j.property] using hp
  have ht : Function.Injective (fun i : R => t i.val) := by
    intro i j hij
    exact hs ((h i.val j.val).mpr hij)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : R => s i.val) (fun i : R => t i.val) hs ht
  refine ⟨σ, fun i => ?_⟩
  have hi := hσ ⟨tupleFirstIndex s i, tupleFirstIndex_idem s i⟩
  dsimp only at hi
  rw [tupleFirstIndex_value s i] at hi
  exact hi.trans ((h _ _).mp (tupleFirstIndex_value s i))

/-- Compression to first-position labels is a literal global permutation on the tuple. -/
theorem tupleFirstIndex_permutation {k : ℕ} (s : Fin k → ℕ) :
    ∃ σ : Equiv.Perm ℕ, ∀ i, σ (s i) = (tupleFirstIndex s i).val := by
  apply tupleLabelPermutation
  intro i j
  exact (tupleFirstIndex_eq_iff s i j).symm.trans Fin.ext_iff

end DittertRybin.Certificates
