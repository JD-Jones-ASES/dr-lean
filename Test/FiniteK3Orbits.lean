import DR.Certificates.FiniteK3Orbits

open DittertRybin.Certificates

-- First-position representatives differ from sequential first-occurrence ranks.
example : tupleFirstIndex (![7,7,9,15] : Fin 4 → Nat) = ![0,0,2,3] := by decide +kernel
example : fourTupleRank ![0,0,2,3] 2 = 1 := by decide +kernel

-- Arbitrarily large and noncontiguous physical labels keep the source's role index.
example : finiteK3Entry (fun i : Fin 93 => i.val)
    (17,5) (17,9) (23,5) (42,9) = 32 := by decide +kernel

example : finiteK3Entry (fun i : Fin 93 => i.val)
    (0,0) (0,0) (0,0) (0,0) = 0 := by decide +kernel

-- Row/column transposition is deliberately not identified with pair reversal.
example : finiteK3Entry (fun i : Fin 93 => i.val)
    (0,0) (0,1) (1,0) (1,1) = 29 ∧
    finiteK3Entry (fun i : Fin 93 => i.val)
    (0,0) (1,0) (0,1) (1,1) = 46 := by decide +kernel

example : finiteK3RoleKeys.get 32 = 329 := by decide +kernel

-- A zero-length tuple needs no inhabitant in its ambient type.
example (s : Fin 0 → Empty) : IsTuplePattern (tupleFirstIndex s) := tupleFirstIndex_isPattern s

-- All equality relations, rather than just distinct-position counts, are preserved.
example {α : Type*} [DecidableEq α] (s : Fin 4 → α) :
    ∃ a : Fin 15, ∀ i j, s i = s j ↔ fourTuplePatterns a i = fourTuplePatterns a j :=
  exists_fourTuplePattern s

#print axioms fourTuplePatterns_complete
#print axioms exists_fourTuplePattern
#print axioms finiteK3RoleTable_key
#print axioms finiteK3RoleTable_surjective
#print axioms finiteK3Entry_swap_multiplier
#print axioms finiteK3Entry_symmetric
#print axioms finiteK3Entry_map
