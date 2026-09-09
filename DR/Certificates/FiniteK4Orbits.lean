import DR.Certificates.FiniteK4OrbitChecks
import Mathlib.Order.Fin.Basic

/-! Universal five-cell roles and the precise four-row restriction.
Surjectivity is verified by one literal witness per role, rather than
trusting the generator's count. No row/column transposition is quotiented. -/

namespace DittertRybin.Certificates
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

theorem finiteK4RoleWitnesses_correct : ∀ k : Fin 407,
    (finiteK4RoleTable.get (finiteK4RoleWitnesses.get k).1).get
      (finiteK4RoleWitnesses.get k).2 = k := by
  intro k
  fin_cases k <;> decide +kernel

private theorem finiteK4RoleKeys_adjacent : ∀ i : Fin 406,
    finiteK4RoleKeys.get i.castSucc < finiteK4RoleKeys.get i.succ := by
  decide +kernel

theorem finiteK4RoleKeys_injective : Function.Injective finiteK4RoleKeys.get :=
  (Fin.strictMono_iff_lt_succ.mpr finiteK4RoleKeys_adjacent).injective

theorem finiteK4FourRowRoleTable_correct : ∀ r : Fin 51, ∀ c : Fin 52,
    finiteK4FourRowRoleIndices.get ((finiteK4FourRowRoleTable.get r).get c) =
      (finiteK4RoleTable.get r.castSucc).get c := by
  intro r
  fin_cases r <;> decide +kernel

theorem finiteK4FourRowRoleWitnesses_correct : ∀ k : Fin 391,
    (finiteK4FourRowRoleTable.get (finiteK4FourRowRoleWitnesses.get k).1).get
      (finiteK4FourRowRoleWitnesses.get k).2 = k := by
  intro k
  fin_cases k <;> decide +kernel

private theorem finiteK4FourRowRoleIndices_adjacent : ∀ i : Fin 390,
    finiteK4FourRowRoleIndices.get i.castSucc < finiteK4FourRowRoleIndices.get i.succ := by
  decide +kernel

theorem finiteK4FourRowRoleIndices_injective :
    Function.Injective finiteK4FourRowRoleIndices.get :=
  (Fin.strictMono_iff_lt_succ.mpr finiteK4FourRowRoleIndices_adjacent).injective

def finiteK4RoleIndex (s : Fin 5 → ℕ × ℕ) : Fin 407 :=
  (finiteK4RoleTable.get (fiveTuplePatternIndex (fun i => (s i).1))).get
    (fiveTuplePatternIndex (fun i => (s i).2))

/-- The finite catalogue index evaluates the actual role formula on all natural labels. -/
theorem finiteK4RoleIndex_spec (s : Fin 5 → ℕ × ℕ) :
    finiteK4TupleRoleKey s = finiteK4RoleKeys.get (finiteK4RoleIndex s) := by
  rw [finiteK4TupleRoleKey_compress, finiteK4RoleTable_correct]
  rfl

theorem finiteK4RoleIndex_congr (s t : Fin 5 → ℕ × ℕ)
    (hr : ∀ i j, (s i).1 = (s j).1 ↔ (t i).1 = (t j).1)
    (hc : ∀ i j, (s i).2 = (s j).2 ↔ (t i).2 = (t j).2) :
    finiteK4RoleIndex s = finiteK4RoleIndex t := by
  apply finiteK4RoleKeys_injective
  rw [← finiteK4RoleIndex_spec, ← finiteK4RoleIndex_spec]
  exact finiteK4TupleRoleKey_congr s t hr hc

theorem finiteK4RoleIndex_pattern (r c : Fin 52) :
    finiteK4RoleIndex (finiteK4PatternCell r c) = (finiteK4RoleTable.get r).get c := by
  apply finiteK4RoleKeys_injective
  rw [← finiteK4RoleIndex_spec, finiteK4RoleTable_correct]

theorem finiteK4RoleIndex_surjective : Function.Surjective finiteK4RoleIndex := by
  intro k
  refine ⟨finiteK4PatternCell (finiteK4RoleWitnesses.get k).1
    (finiteK4RoleWitnesses.get k).2, ?_⟩
  rw [finiteK4RoleIndex_pattern, finiteK4RoleWitnesses_correct]

/-- A repeated row label puts the role in exactly the 391-entry four-row subcatalogue. -/
theorem finiteK4RoleIndex_fourRows (s : Fin 5 → ℕ × ℕ)
    (hr : ¬Function.Injective (fun i => (s i).1)) :
    ∃ k : Fin 391, finiteK4FourRowRoleIndices.get k = finiteK4RoleIndex s := by
  let r : Fin 51 := ⟨(fiveTuplePatternIndex (fun i => (s i).1)).val,
    fiveTuplePatternIndex_lt_fiftyOne _ hr⟩
  let c := fiveTuplePatternIndex (fun i => (s i).2)
  refine ⟨(finiteK4FourRowRoleTable.get r).get c, ?_⟩
  rw [finiteK4FourRowRoleTable_correct]
  rfl

/-- This is the physical four-row restriction, with arbitrary column count. -/
theorem finiteK4RoleIndex_finFour {n : ℕ} (s : Fin 5 → Fin 4 × Fin n) :
    ∃ k : Fin 391, finiteK4FourRowRoleIndices.get k =
      finiteK4RoleIndex (fun i => ((s i).1.val, (s i).2.val)) := by
  apply finiteK4RoleIndex_fourRows
  intro h
  have hi : Function.Injective (fun i => (s i).1) := by
    intro i j hij
    exact h (congrArg Fin.val hij)
  have hc := Fintype.card_le_of_injective _ hi
  norm_num at hc

end
end DittertRybin.Certificates
