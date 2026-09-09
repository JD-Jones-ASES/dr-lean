import DR.Square.OrderThreeCanonical
import Mathlib.Data.Fintype.Prod

/-!
# Finite order-three support classification

This is a kernel-evaluated exhaustion of the 512 Boolean support masks.
The classification is finite; the real-valued face inequalities are proved
separately. Boundary entries in the singleton and disconnected cases remain
unrestricted where the corresponding real inequalities allow them.
-/

namespace DittertRybin

def orderThreeAxisMap (r : Fin 6) : Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]] r

theorem orderThreeAxisMap_bijective (r : Fin 6) : Function.Bijective (orderThreeAxisMap r) := by
  fin_cases r <;> decide

noncomputable def orderThreeAxisEquiv (r : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (orderThreeAxisMap r) (orderThreeAxisMap_bijective r)

def orderThreeReorient {α : Type*} (A : Fin 3 → Fin 3 → α)
    (r c : Fin 6) (t : Bool) : Fin 3 → Fin 3 → α :=
  if t then fun i j => A (orderThreeAxisMap r j) (orderThreeAxisMap c i)
  else fun i j => A (orderThreeAxisMap r i) (orderThreeAxisMap c j)

inductive OrderThreeSupportKind
  | full | zero11 | zero12 | zero22 | twoProper | cycle | singletonOpposite
  | containing | twoSingletons | disjointSquare | disjointCross
  deriving DecidableEq

instance : Fintype OrderThreeSupportKind where
  elems := {.full, .zero11, .zero12, .zero22, .twoProper, .cycle, .singletonOpposite,
    .containing, .twoSingletons, .disjointSquare, .disjointCross}
  complete k := by cases k <;> simp

def OrderThreeFitsSupport (P : Fin 3 → Fin 3 → Bool) : OrderThreeSupportKind → Prop
  | .full => ∀ i j, P i j = true
  | .zero11 => P = ![![false,true,true], ![true,true,true], ![true,true,true]]
  | .zero12 => P = ![![false,false,true], ![true,true,true], ![true,true,true]]
  | .zero22 => P = ![![false,false,true], ![false,false,true], ![true,true,true]]
  | .twoProper => P = ![![false,true,true], ![true,true,true], ![true,false,true]]
  | .cycle => P = ![![false,true,true], ![true,true,false], ![true,false,true]]
  | .singletonOpposite => P = ![![true,false,true], ![false,true,true], ![false,true,true]]
  | .containing => P 0 0 = true ∧ P 0 1 = true ∧ P 1 1 = true ∧ P 2 2 = true ∧
      P 1 0 = false ∧ P 2 0 = false ∧ P 2 1 = false
  | .twoSingletons => P 0 0 = true ∧ P 1 1 = true ∧ P 2 2 = true ∧
      P 0 1 = false ∧ P 1 0 = false ∧ P 2 0 = false ∧ P 2 1 = false
  | .disjointSquare => P 0 1 = false ∧ P 0 2 = false ∧ P 1 0 = false ∧ P 2 0 = false
  | .disjointCross => P 0 2 = false ∧ P 1 0 = false ∧ P 1 1 = false ∧
      P 2 0 = false ∧ P 2 1 = false

instance (P : Fin 3 → Fin 3 → Bool) (k : OrderThreeSupportKind) :
    Decidable (OrderThreeFitsSupport P k) := by cases k <;> dsimp only [OrderThreeFitsSupport] <;> infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- Every mask with no empty row or column belongs to an explicitly proved
canonical support family after permutations and optional transposition. -/
theorem orderThree_boolean_support_classification :
    ∀ P : Fin 3 → Fin 3 → Bool,
      (∀ i, ∃ j, P i j = true) → (∀ j, ∃ i, P i j = true) →
      ∃ r c : Fin 6, ∃ t : Bool, ∃ k : OrderThreeSupportKind,
        OrderThreeFitsSupport (orderThreeReorient P r c t) k := by
  intro P
  have hP : P = ![![P 0 0, P 0 1, P 0 2], ![P 1 0, P 1 1, P 1 2], ![P 2 0, P 2 1, P 2 2]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hP]
  generalize P 0 0 = a, P 0 1 = b, P 0 2 = c, P 1 0 = d, P 1 1 = e,
    P 1 2 = f, P 2 0 = g, P 2 1 = h, P 2 2 = i
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    cases f <;> cases g <;> cases h <;> cases i <;> decide +kernel

end DittertRybin
