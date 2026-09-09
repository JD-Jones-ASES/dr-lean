import DR.Certificates.FiniteK3OrbitData
import Mathlib.Data.Fintype.Prod

/-!
# Exact pair-role semantics for the finite K=3 certificates

Four-position first-index compression gives all fifteen equality patterns
on each axis. Sequential ranks recover the source's displayed canonical key.
The 225-entry table is checked against that key, and its two pair symmetries
transfer to arbitrary ambient row and column types.
-/

namespace DittertRybin.Certificates

def fourTupleRank (p : Fin 4 → Fin 4) (i : Fin 4) : Nat :=
  (Finset.univ.filter fun j => j < p i ∧ p j = j).card

def finiteK3NormalizedKey (r c : Fin 4 → Fin 4) : Nat :=
  let cell := fun i => 4 * fourTupleRank (tupleFirstIndex r) i +
    fourTupleRank (tupleFirstIndex c) i
  16^3 * cell 0 + 16^2 * cell 1 + 16 * cell 2 + cell 3

def finiteK3SwapFirst : Fin 4 → Fin 4 := ![1,0,2,3]
def finiteK3SwapLast : Fin 4 → Fin 4 := ![0,1,3,2]

def finiteK3CanonicalKey (r c : Fin 4 → Fin 4) : Nat :=
  min (min (finiteK3NormalizedKey r c)
    (finiteK3NormalizedKey (r ∘ finiteK3SwapFirst) (c ∘ finiteK3SwapFirst)))
    (min (finiteK3NormalizedKey (r ∘ finiteK3SwapLast) (c ∘ finiteK3SwapLast))
      (finiteK3NormalizedKey (r ∘ finiteK3SwapFirst ∘ finiteK3SwapLast)
        (c ∘ finiteK3SwapFirst ∘ finiteK3SwapLast)))

def finiteK3TableRole (r c : Fin 15) : Fin 93 := (finiteK3RoleTable.get r).get c

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3RoleTable_key : ∀ r c : Fin 15,
    finiteK3RoleKeys.get (finiteK3TableRole r c) =
      finiteK3CanonicalKey (fourTuplePatterns r) (fourTuplePatterns c) := by
  decide +kernel

theorem finiteK3RoleKeys_injective : Function.Injective finiteK3RoleKeys.get := by
  decide +kernel

theorem finiteK3RoleTable_surjective : Function.Surjective finiteK3TableRole.uncurry := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3RoleTable_swapFirst : ∀ r c : Fin 15,
    finiteK3TableRole (fourTuplePatternIndex (fourTuplePatterns r ∘ finiteK3SwapFirst))
      (fourTuplePatternIndex (fourTuplePatterns c ∘ finiteK3SwapFirst)) =
        finiteK3TableRole r c := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteK3RoleTable_swapLast : ∀ r c : Fin 15,
    finiteK3TableRole (fourTuplePatternIndex (fourTuplePatterns r ∘ finiteK3SwapLast))
      (fourTuplePatternIndex (fourTuplePatterns c ∘ finiteK3SwapLast)) =
        finiteK3TableRole r c := by
  decide +kernel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The physical coefficient role depends only on equality of the actual labels. -/
def finiteK3Role (r : Fin 4 → α) (c : Fin 4 → β) : Fin 93 :=
  finiteK3TableRole (fourTuplePatternIndex r) (fourTuplePatternIndex c)

theorem finiteK3Role_swapFirst (r : Fin 4 → α) (c : Fin 4 → β) :
    finiteK3Role (r ∘ finiteK3SwapFirst) (c ∘ finiteK3SwapFirst) = finiteK3Role r c := by
  unfold finiteK3Role
  rw [fourTuplePatternIndex_comp r, fourTuplePatternIndex_comp c]
  exact finiteK3RoleTable_swapFirst _ _

theorem finiteK3Role_swapLast (r : Fin 4 → α) (c : Fin 4 → β) :
    finiteK3Role (r ∘ finiteK3SwapLast) (c ∘ finiteK3SwapLast) = finiteK3Role r c := by
  unfold finiteK3Role
  rw [fourTuplePatternIndex_comp r, fourTuplePatternIndex_comp c]
  exact finiteK3RoleTable_swapLast _ _

theorem finiteK3Role_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (r : Fin 4 → α) (c : Fin 4 → β) (r' : Fin 4 → α') (c' : Fin 4 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) : finiteK3Role r c = finiteK3Role r' c' := by
  unfold finiteK3Role
  rw [fourTuplePatternIndex_congr r r' hr, fourTuplePatternIndex_congr c c' hc]

omit [DecidableEq α] in
theorem tuple_comp_swapFirst (e f a b : α) :
    (![e,f,a,b] : Fin 4 → α) ∘ finiteK3SwapFirst = ![f,e,a,b] := by
  funext i
  fin_cases i <;> rfl

omit [DecidableEq α] in
theorem tuple_comp_swapLast (e f a b : α) :
    (![e,f,a,b] : Fin 4 → α) ∘ finiteK3SwapLast = ![e,f,b,a] := by
  funext i
  fin_cases i <;> rfl

/-- Actual seed entry for any row/column dimensions and any coefficient ring. -/
def finiteK3Entry {R : Type*} (coefficients : Fin 93 → R) (e f a b : α × β) : R :=
  coefficients (finiteK3Role ![e.1,f.1,a.1,b.1] ![e.2,f.2,a.2,b.2])

theorem finiteK3Entry_swap_multiplier {R : Type*} (coefficients : Fin 93 → R)
    (e f a b : α × β) : finiteK3Entry coefficients f e a b = finiteK3Entry coefficients e f a b := by
  have h := finiteK3Role_swapFirst (![e.1,f.1,a.1,b.1] : Fin 4 → α)
    (![e.2,f.2,a.2,b.2] : Fin 4 → β)
  rw [tuple_comp_swapFirst, tuple_comp_swapFirst] at h
  exact congrArg coefficients h

theorem finiteK3Entry_symmetric {R : Type*} (coefficients : Fin 93 → R)
    (e f a b : α × β) : finiteK3Entry coefficients e f b a = finiteK3Entry coefficients e f a b := by
  have h := finiteK3Role_swapLast (![e.1,f.1,a.1,b.1] : Fin 4 → α)
    (![e.2,f.2,a.2,b.2] : Fin 4 → β)
  rw [tuple_comp_swapLast, tuple_comp_swapLast] at h
  exact congrArg coefficients h

theorem finiteK3Entry_map {R α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (coefficients : Fin 93 → R) (u : α → α') (v : β → β')
    (hu : Function.Injective u) (hv : Function.Injective v) (e f a b : α × β) :
    finiteK3Entry coefficients (u e.1,v e.2) (u f.1,v f.2)
      (u a.1,v a.2) (u b.1,v b.2) = finiteK3Entry coefficients e f a b := by
  apply congrArg coefficients
  apply finiteK3Role_congr
  · intro i j
    have h (i : Fin 4) : (![u e.1,u f.1,u a.1,u b.1] : Fin 4 → α') i =
        u ((![e.1,f.1,a.1,b.1] : Fin 4 → α) i) := by fin_cases i <;> rfl
    rw [h i,h j]
    exact hu.eq_iff
  · intro i j
    have h (i : Fin 4) : (![v e.2,v f.2,v a.2,v b.2] : Fin 4 → β') i =
        v ((![e.2,f.2,a.2,b.2] : Fin 4 → β) i) := by fin_cases i <;> rfl
    rw [h i,h j]
    exact hv.eq_iff

end DittertRybin.Certificates
