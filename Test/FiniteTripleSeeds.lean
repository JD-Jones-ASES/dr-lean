import DR.Certificates.FiniteTripleSeeds

namespace DittertRybin.Tests
open Certificates

-- A full host needs no spare label to extend a tuple correspondence.
example : ∃ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3, σ i = ![2,0,1] i := by
  apply tupleHostPermutation (fun i : Fin 3 => i) (![2,0,1] : Fin 3 → Fin 3)
  decide +kernel

-- The empty tuple on the empty host also has a genuine host permutation.
example : ∃ σ : Equiv.Perm (Fin 0), ∀ i : Fin 0, σ i = i := by
  exact tupleHostPermutation (fun i : Fin 0 => i) (fun i => i) (fun _ _ => Iff.rfl)

-- Repeated cells are not three independent marked positions.
example : finiteTripleSeed 0 0 = finiteTripleSeed 0 2 := by decide +kernel
example : (finiteTripleSeed 4 0).1 = (finiteTripleSeed 4 2).1 ∧
    finiteTripleSeed 4 0 ≠ finiteTripleSeed 4 2 := by decide +kernel
example : ¬ (∀ i j : Fin 3, (finiteTripleSeed 0 i).2 = (finiteTripleSeed 0 j).2 ↔
    (finiteTripleSeed 4 i).2 = (finiteTripleSeed 4 j).2) := by decide +kernel

-- Every one of the ten seeds is a literal physical triple already on 3-by-3.
example : ∀ a : Fin 10, ∀ i : Fin 3,
    finiteTriplePhysicalSeed (by decide : 3 ≤ 3) (by decide : 3 ≤ 3) a i = finiteTripleSeed a i := by
  decide +kernel

-- Coverage applies to arbitrary actual finite row and column indices.
example (t : Fin 3 → Fin 4 × Fin 5) :
    ∃ a : Fin 10, ∃ σ : Equiv.Perm (Fin 3), ∃ ρ : Equiv.Perm (Fin 4),
      ∃ κ : Equiv.Perm (Fin 5), ∀ i,
        Prod.map ρ κ (t (σ i)) = finiteTriplePhysicalSeed (by decide) (by decide) a i :=
  finiteTripleSeed_physical_coverage (by decide) (by decide) t

#print axioms tupleHostPermutation
#print axioms threeTuplePatterns_complete
#print axioms finiteTripleOrder_bijective
#print axioms finiteTripleSeed_mark
#print axioms finiteTripleSeed_pattern_coverage
#print axioms finiteTripleSeed_physical_coverage
end DittertRybin.Tests
