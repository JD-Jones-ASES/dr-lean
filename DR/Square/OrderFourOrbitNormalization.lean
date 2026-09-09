import DR.Certificates.SpectralFourDefinitions
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Semantic row/column invariance of the order-four certificate keys

First-occurrence labeling depends only on equality of labels. Consequently
injective relabeling leaves it unchanged. The finite physical permutations
below extend to permutations of natural labels so that no support or
occurrence assumption is hidden in the normalization argument.
-/

namespace DittertRybin

open Certificates

theorem orderFour_idxOf_map_injective (f : ℕ → ℕ) (hf : Function.Injective f)
    (xs : List ℕ) (x : ℕ) : (xs.map f).idxOf (f x) = xs.idxOf x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.idxOf_cons, cond_eq_ite, beq_iff_eq, hf.eq_iff, ih]

private noncomputable def firstOccurrenceStep (state : List ℕ × List ℕ) (x : ℕ) : List ℕ × List ℕ :=
  if x ∈ state.1 then (state.1, state.2 ++ [state.1.idxOf x])
  else (state.1 ++ [x], state.2 ++ [state.1.length])

theorem firstOccurrenceLabels_map_injective (f : ℕ → ℕ) (hf : Function.Injective f)
    (xs : List ℕ) : firstOccurrenceLabels (xs.map f) = firstOccurrenceLabels xs := by
  have hstep (st : List ℕ × List ℕ) (x : ℕ) :
      firstOccurrenceStep (st.1.map f, st.2) (f x) =
        ((firstOccurrenceStep st x).1.map f, (firstOccurrenceStep st x).2) := by
    rcases st with ⟨seen, out⟩
    have hmem : f x ∈ seen.map f ↔ x ∈ seen := by simp [List.mem_map, hf.eq_iff]
    by_cases hx : x ∈ seen <;>
      simp [firstOccurrenceStep, hmem, hx, orderFour_idxOf_map_injective f hf]
  have h := List.foldl_hom (fun st : List ℕ × List ℕ => (st.1.map f, st.2))
    (g₁ := firstOccurrenceStep) (g₂ := fun st x => firstOccurrenceStep st (f x))
    (l := xs) (init := ([], [])) hstep
  change ((xs.map f).foldl firstOccurrenceStep ([], [])).2 =
    (xs.foldl firstOccurrenceStep ([], [])).2
  rw [List.foldl_map]
  have hh := congrArg (fun st : List ℕ × List ℕ => st.2) h
  simpa only [List.map_nil] using hh

theorem spectralFourNormalizedKey_map (f g T : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) (cells : List ℕ)
    (hrow : ∀ a ∈ cells, T a / 4 = f (a / 4))
    (hcol : ∀ a ∈ cells, T a % 4 = g (a % 4)) :
    spectralFourNormalizedKey (cells.map T) = spectralFourNormalizedKey cells := by
  have hr : (cells.map T).map (· / 4) = (cells.map (· / 4)).map f := by
    simp only [List.map_map]
    exact List.map_congr_left hrow
  have hc : (cells.map T).map (· % 4) = (cells.map (· % 4)).map g := by
    simp only [List.map_map]
    exact List.map_congr_left hcol
  unfold spectralFourNormalizedKey
  rw [hr, hc, firstOccurrenceLabels_map_injective f hf, firstOccurrenceLabels_map_injective g hg]

/-- Extend a permutation of four labels by the identity on every larger natural. -/
def orderFourExtendLabel (r : Equiv.Perm (Fin 4)) (a : ℕ) : ℕ :=
  if h : a < 4 then (r ⟨a,h⟩).val else a

theorem orderFourExtendLabel_lt (r : Equiv.Perm (Fin 4)) {a : ℕ} (ha : a < 4) :
    orderFourExtendLabel r a < 4 := by
  simp [orderFourExtendLabel, ha]

theorem orderFourExtendLabel_inverse (r : Equiv.Perm (Fin 4)) (a : ℕ) :
    orderFourExtendLabel r.symm (orderFourExtendLabel r a) = a := by
  by_cases ha : a < 4
  · simp [orderFourExtendLabel, ha, (r ⟨a,ha⟩).isLt]
  · simp [orderFourExtendLabel, ha]

theorem orderFourExtendLabel_injective (r : Equiv.Perm (Fin 4)) :
    Function.Injective (orderFourExtendLabel r) :=
  Function.LeftInverse.injective (orderFourExtendLabel_inverse r)

def orderFourCellMapNat (r c : Equiv.Perm (Fin 4)) (a : ℕ) : ℕ :=
  4 * orderFourExtendLabel r (a / 4) + orderFourExtendLabel c (a % 4)

theorem orderFourCellMapNat_div (r c : Equiv.Perm (Fin 4)) (a : ℕ) :
    orderFourCellMapNat r c a / 4 = orderFourExtendLabel r (a / 4) := by
  have h := orderFourExtendLabel_lt c (Nat.mod_lt a (by decide : 0 < 4))
  unfold orderFourCellMapNat
  omega

theorem orderFourCellMapNat_mod (r c : Equiv.Perm (Fin 4)) (a : ℕ) :
    orderFourCellMapNat r c a % 4 = orderFourExtendLabel c (a % 4) := by
  have h := orderFourExtendLabel_lt c (Nat.mod_lt a (by decide : 0 < 4))
  unfold orderFourCellMapNat
  omega

theorem orderFourCellMapNat_inverse (r c : Equiv.Perm (Fin 4)) (a : ℕ) :
    orderFourCellMapNat r.symm c.symm (orderFourCellMapNat r c a) = a := by
  rw [orderFourCellMapNat, orderFourCellMapNat_div, orderFourCellMapNat_mod,
    orderFourExtendLabel_inverse, orderFourExtendLabel_inverse]
  omega

theorem orderFourCellMapNat_lt (r c : Equiv.Perm (Fin 4)) {a : ℕ} (ha : a < 16) :
    orderFourCellMapNat r c a < 16 := by
  have hr := orderFourExtendLabel_lt r (show a / 4 < 4 by omega)
  have hc := orderFourExtendLabel_lt c (Nat.mod_lt a (by decide : 0 < 4))
  unfold orderFourCellMapNat
  omega

def orderFourPhysicalPermutation (r c : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 16) where
  toFun a := ⟨orderFourCellMapNat r c a.val, orderFourCellMapNat_lt r c a.isLt⟩
  invFun a := ⟨orderFourCellMapNat r.symm c.symm a.val, orderFourCellMapNat_lt r.symm c.symm a.isLt⟩
  left_inv a := Fin.ext (orderFourCellMapNat_inverse r c a.val)
  right_inv a := by
    apply Fin.ext
    simpa using orderFourCellMapNat_inverse r.symm c.symm a.val

/-- Physical row and column permutations leave the documented key unchanged. -/
theorem spectralFourNormalizedKey_physical (r c : Equiv.Perm (Fin 4)) (cells : List ℕ) :
    spectralFourNormalizedKey (cells.map (orderFourCellMapNat r c)) =
      spectralFourNormalizedKey cells :=
  spectralFourNormalizedKey_map _ _ _ (orderFourExtendLabel_injective r)
    (orderFourExtendLabel_injective c) cells
    (fun a _ => orderFourCellMapNat_div r c a)
    (fun a _ => orderFourCellMapNat_mod r c a)

end DittertRybin
