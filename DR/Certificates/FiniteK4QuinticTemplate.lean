import DR.Certificates.FiniteK4QuinticData

/-! The literal local quintic gates retain ten role choices and ten sparse
slots. Every physical role and repeated-cell weight is checked against its
actual formula; selector fibers account for every choice including padding. -/
namespace DittertRybin.Certificates
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteK4QuinticPairIndex (r c : Fin 52) : Fin 2704 := ⟨52*r.val+c.val, by omega⟩

def finiteK4QuinticEquation (r c : Fin 52) : Fin 91 :=
  (finiteK4QuinticPatternEquation.get r).get c

def finiteK4QuinticOrderedPattern (r : Fin 52) (q : Fin 10) : Fin 52 :=
  (finiteK4QuinticTriplePatterns.get r).get q

def finiteK4QuinticRole (r c : Fin 52) (q : Fin 10) : Fin 407 :=
  (finiteK4QuinticTripleRoles.get (finiteK4QuinticPairIndex r c)).get q

def finiteK4QuinticWeight (r c : Fin 52) (q : Fin 10) : Nat :=
  (finiteK4QuinticTripleWeights.get (finiteK4QuinticPairIndex r c)).get q

def finiteK4QuinticSlot (r c : Fin 52) (q : Fin 10) : Fin 10 :=
  (finiteK4QuinticTripleSlots.get (finiteK4QuinticPairIndex r c)).get q

def finiteK4QuinticTerm (a : Fin 91) (k : Fin 10) : Fin 407 × Nat :=
  (finiteK4QuinticRowTerms.get a).get k

def FiniteK4QuinticPatternCorrect (r c : Fin 52) : Prop :=
  (∀ q : Fin 10, (finiteK4RoleTable.get (finiteK4QuinticOrderedPattern r q)).get
      (finiteK4QuinticOrderedPattern c q) = finiteK4QuinticRole r c q) ∧
  (∀ q : Fin 10, finiteK4MultiplierWeight (fiveTuplePatterns r ∘ finiteK4TripleOrder q)
      (fiveTuplePatterns c ∘ finiteK4TripleOrder q) = finiteK4QuinticWeight r c q) ∧
  (∀ q : Fin 10, finiteK4QuinticRole r c q =
      (finiteK4QuinticTerm (finiteK4QuinticEquation r c) (finiteK4QuinticSlot r c q)).1) ∧
  (∀ k : Fin 10, finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation r c) *
      (∑ q : Fin 10, if finiteK4QuinticSlot r c q = k then finiteK4QuinticWeight r c q else 0) =
        60 * (finiteK4QuinticTerm (finiteK4QuinticEquation r c) k).2) ∧
  (∑ a : Fin 5, finiteK4DeletedSuccess (fiveTuplePatterns r) (fiveTuplePatterns c) a) =
      finiteK4QuinticDeletedSuccesses.get (finiteK4QuinticPairIndex r c) ∧
  finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation r c) * 12 *
      finiteK4QuinticDeletedSuccesses.get (finiteK4QuinticPairIndex r c) =
        60 * finiteK4QuinticSuccesses.get (finiteK4QuinticEquation r c)

instance (r c : Fin 52) : Decidable (FiniteK4QuinticPatternCorrect r c) := by
  unfold FiniteK4QuinticPatternCorrect
  infer_instance

theorem finiteK4QuinticOrderedPattern_compression : ∀ r : Fin 52, ∀ q : Fin 10,
    tupleFirstIndex (fiveTuplePatterns r ∘ finiteK4TripleOrder q) =
      fiveTuplePatterns (finiteK4QuinticOrderedPattern r q) := by
  decide +kernel

theorem finiteK4QuinticOrderedPattern_index (r : Fin 52) (q : Fin 10) :
    fiveTuplePatternIndex (fiveTuplePatterns r ∘ finiteK4TripleOrder q) =
      finiteK4QuinticOrderedPattern r q := by
  apply fiveTuplePatterns_injective
  rw [fiveTuplePatternIndex_spec,finiteK4QuinticOrderedPattern_compression]

theorem finiteK4QuinticMultiplicity_pos : ∀ a : Fin 91, 0 < finiteK4QuinticMultiplicity.get a := by
  decide +kernel

end DittertRybin.Certificates
