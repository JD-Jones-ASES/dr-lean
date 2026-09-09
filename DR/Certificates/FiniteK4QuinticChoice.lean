import DR.Certificates.FiniteK4Orbits
import Mathlib.Algebra.BigOperators.Fin

/-! Ten choices of the multiplier triple and the actual deleted-four event.
Each chosen order is a permutation of all five physical sample positions.
The integer correction is six times the ordered-triple weight, including
triple and double repetitions. This module asserts no certificate identity. -/

namespace DittertRybin.Certificates

/-- Increasing multiplier positions, followed by increasing complementary positions. -/
def finiteK4TripleOrder : Fin 10 → (Fin 5 → Fin 5) :=
  ![![0,1,2,3,4], ![0,1,3,2,4], ![0,1,4,2,3], ![0,2,3,1,4], ![0,2,4,1,3], ![0,3,4,1,2], ![1,2,3,0,4], ![1,2,4,0,3], ![1,3,4,0,2], ![2,3,4,0,1]]

theorem finiteK4TripleOrder_bijective : ∀ q : Fin 10,
    Function.Bijective (finiteK4TripleOrder q) := by
  decide +kernel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Six, two, or one according to the multiplicities of the first three cells. -/
def finiteK4MultiplierWeight (r : Fin 5 → α) (c : Fin 5 → β) : Nat :=
  if (r 0 = r 1 ∧ c 0 = c 1) ∧ (r 1 = r 2 ∧ c 1 = c 2) then 6
  else if (r 0 = r 1 ∧ c 0 = c 1) ∨ (r 0 = r 2 ∧ c 0 = c 2) ∨
    (r 1 = r 2 ∧ c 1 = c 2) then 2 else 1

/-- Inclusive OR on the four positions retained after deleting a. -/
def finiteK4DeletedSuccess (r : Fin 5 → α) (c : Fin 5 → β) (a : Fin 5) : Nat :=
  if Function.Injective (r ∘ a.succAbove) ∨ Function.Injective (c ∘ a.succAbove)
    then 1 else 0

theorem finiteK4MultiplierWeight_pos (r : Fin 5 → α) (c : Fin 5 → β) :
    0 < finiteK4MultiplierWeight r c := by
  unfold finiteK4MultiplierWeight
  split_ifs <;> norm_num

theorem finiteK4MultiplierWeight_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (r : Fin 5 → α) (c : Fin 5 → β) (r' : Fin 5 → α') (c' : Fin 5 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) :
    finiteK4MultiplierWeight r c = finiteK4MultiplierWeight r' c' := by
  simp only [finiteK4MultiplierWeight, hr, hc]

theorem finiteK4DeletedSuccess_congr {α' β' : Type*} [DecidableEq α'] [DecidableEq β']
    (r : Fin 5 → α) (c : Fin 5 → β) (r' : Fin 5 → α') (c' : Fin 5 → β')
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j) (a : Fin 5) :
    finiteK4DeletedSuccess r c a = finiteK4DeletedSuccess r' c' a := by
  have hri : Function.Injective (r ∘ a.succAbove) ↔ Function.Injective (r' ∘ a.succAbove) := by
    simp only [Function.Injective, Function.comp_apply, hr]
  have hci : Function.Injective (c ∘ a.succAbove) ↔ Function.Injective (c' ∘ a.succAbove) := by
    simp only [Function.Injective, Function.comp_apply, hc]
  simp only [finiteK4DeletedSuccess, hri, hci]

end DittertRybin.Certificates
