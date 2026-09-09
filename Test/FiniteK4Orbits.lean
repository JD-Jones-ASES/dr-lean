import DR.Certificates.FiniteK4Orbits

open DittertRybin DittertRybin.Certificates

-- Equalities, not the size or order of natural labels, determine the role.
example : finiteK4TupleRoleKey ![(70,9),(70,9),(2,4),(70,4),(2,9)] =
    finiteK4TupleRoleKey ![(0,0),(0,0),(1,1),(0,1),(1,0)] := by
  apply finiteK4TupleRoleKey_congr <;>
    intro i j <;> fin_cases i <;> fin_cases j <;> decide

-- The catalogue keeps row/column transposition separate.
example : finiteK4TupleRoleKey ![(0,0),(1,0),(2,0),(3,0),(4,0)] = 84770 := by
  decide +kernel
example : finiteK4TupleRoleKey ![(0,0),(0,1),(0,2),(0,3),(0,4)] = 16954 := by
  decide +kernel
example : finiteK4TupleRoleKey ![(0,0),(1,0),(2,0),(3,0),(4,0)] ≠
    finiteK4TupleRoleKey ![(0,0),(0,1),(0,2),(0,3),(0,4)] := by
  decide +kernel

-- Five distinct labels occupy the excluded last row pattern; a repeated
-- label at the final position remains in the four-row catalogue.
example : fiveTuplePatternIndex (![0,1,2,3,4] : Fin 5 → Fin 5) = 51 := by
  exact fiveTuplePatternIndex_pattern 51
example : (fiveTuplePatternIndex (![0,1,2,3,0] : Fin 5 → Fin 5)).val < 51 := by
  apply fiveTuplePatternIndex_lt_fiftyOne
  intro h
  have he := h (show (![0,1,2,3,0] : Fin 5 → Fin 5) 0 =
    (![0,1,2,3,0] : Fin 5 → Fin 5) 4 from rfl)
  exact (by decide : (0 : Fin 5) ≠ 4) he

-- The global permutation extension covers empty tuples and forbids collapse.
example (s t : Fin 0 → ℕ) : ∃ σ : Equiv.Perm ℕ, ∀ i, σ (s i) = t i := by
  apply tupleLabelPermutation
  intro i
  exact Fin.elim0 i
example : ¬∃ σ : Equiv.Perm ℕ, σ 3 = 2 ∧ σ 4 = 2 := by
  rintro ⟨σ, h3, h4⟩
  have h := σ.injective (h3.trans h4.symm)
  exact (by decide : (3 : ℕ) ≠ 4) h

-- The four-row restriction holds for every physical column count.
example {n : ℕ} (s : Fin 5 → Fin 4 × Fin n) :
    ∃ k : Fin 391, finiteK4FourRowRoleIndices.get k =
      finiteK4RoleIndex (fun i => ((s i).1.val, (s i).2.val)) :=
  finiteK4RoleIndex_finFour s

#print axioms tupleLabelPermutation
#print axioms fiveTuplePatterns_complete
#print axioms finiteK4TupleRoleKey_congr
#print axioms finiteK4RoleTable_correct
#print axioms finiteK4RoleIndex_spec
#print axioms finiteK4RoleIndex_surjective
#print axioms finiteK4RoleIndex_finFour
