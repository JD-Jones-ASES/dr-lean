import DR.Certificates.FiniteTuplePattern
import Mathlib.Logic.Equiv.Fintype

/-! Equality-preserving relabelings of a finite tuple extend to a permutation
of its actual host type, including a finite row or column index type.
No spare labels, nonempty host or distinct-tuple assumption is required. -/
namespace DittertRybin.Certificates

/-- The two tuples have the same equality relation on positions. -/
theorem tupleHostPermutation {α : Type*} {k : ℕ} (s t : Fin k → α)
    (h : ∀ i j, s i = s j ↔ t i = t j) :
    ∃ σ : Equiv.Perm α, ∀ i, σ (s i) = t i := by
  classical
  let R := {i : Fin k // tupleFirstIndex s i = i}
  have hs : Function.Injective (fun i : R => s i.val) := by
    intro i j hij
    apply Subtype.ext
    have hp := (tupleFirstIndex_eq_iff s i.val j.val).mpr hij
    simpa only [i.property,j.property] using hp
  have ht : Function.Injective (fun i : R => t i.val) := by
    intro i j hij
    exact hs ((h i.val j.val).mpr hij)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : R => s i.val) (fun i : R => t i.val) hs ht
  refine ⟨σ,fun i => ?_⟩
  have hi := hσ ⟨tupleFirstIndex s i,tupleFirstIndex_idem s i⟩
  dsimp only at hi
  rw [tupleFirstIndex_value s i] at hi
  exact hi.trans ((h _ _).mp (tupleFirstIndex_value s i))

end DittertRybin.Certificates
