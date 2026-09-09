import DR.Rectangular.FourRowFiniteSeeds
import DR.Certificates.TwoAxisOrdinaryBlocks

/-! The literal ten-seed role kernel in the reusable ordinary-pair representation. -/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFinitePairLabels {r : ℕ} : OrdinaryPair (Fin r) → ℕ × ℕ
  | .dist i j => (i.val,j.val)
  | .toOrdinary i => (i.val,r)
  | .fromOrdinary j => (r,j.val)
  | .same => (r,r)
  | .different => (r,r+1)

def fourRowFiniteSeedPairKey (s : Fin 10)
    (r : OrdinaryPair (Fin (fourRowFiniteSeedRows s)))
    (c : OrdinaryPair (Fin (fourRowFiniteSeedColumns s))) : ℕ :=
  fourRowFiniteCanonicalRoleKey (fourRowFiniteSeedMark s)
    ((fourRowFinitePairLabels r).1,(fourRowFinitePairLabels c).1)
    ((fourRowFinitePairLabels r).2,(fourRowFinitePairLabels c).2)

def fourRowFiniteSeedRelationKernel (s : Fin 10) (h : ℕ → ℝ) :
    OrdinaryPair (Fin (fourRowFiniteSeedRows s)) →
      OrdinaryPair (Fin (fourRowFiniteSeedColumns s)) → ℝ :=
  fun r c => h (fourRowFiniteSeedPairKey s r c)

def fourRowFinitePairSwapLabel {r : ℕ} : OrdinaryPair (Fin r) → Equiv.Perm ℕ
  | .different => Equiv.swap r (r+1)
  | _ => Equiv.refl ℕ

theorem fourRowFinitePairSwapLabel_fixed {r : ℕ} (p : OrdinaryPair (Fin r))
    {i : ℕ} (hi : i < r) : fourRowFinitePairSwapLabel p i = i := by
  cases p <;> simp [fourRowFinitePairSwapLabel, Equiv.swap_apply_def,
    Nat.ne_of_lt hi, show i ≠ r+1 by omega]

theorem fourRowFinitePairLabels_swap {r : ℕ} (p : OrdinaryPair (Fin r)) :
    fourRowFinitePairLabels p.swap =
      (fourRowFinitePairSwapLabel p (fourRowFinitePairLabels p).2,
        fourRowFinitePairSwapLabel p (fourRowFinitePairLabels p).1) := by
  cases p <;> simp [fourRowFinitePairLabels, fourRowFinitePairSwapLabel, OrdinaryPair.swap]

theorem fourRowFiniteSeedPairKey_swap (s : Fin 10)
    (r : OrdinaryPair (Fin (fourRowFiniteSeedRows s)))
    (c : OrdinaryPair (Fin (fourRowFiniteSeedColumns s))) :
    fourRowFiniteSeedPairKey s r.swap c.swap = fourRowFiniteSeedPairKey s r c := by
  have hm : (fourRowFiniteSeedMark s).map
      (Prod.map (fourRowFinitePairSwapLabel r) (fourRowFinitePairSwapLabel c)) =
      fourRowFiniteSeedMark s := by
    conv_rhs => rw [← List.map_id (fourRowFiniteSeedMark s)]
    apply List.map_congr_left
    intro p hp
    have hr : p.1 < fourRowFiniteSeedRows s := by
      apply Finset.mem_range.mp
      rw [← (fourRowFiniteSeed_labels s).1]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem hp)
    have hc : p.2 < fourRowFiniteSeedColumns s := by
      apply Finset.mem_range.mp
      rw [← (fourRowFiniteSeed_labels s).2]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem hp)
    exact Prod.ext (fourRowFinitePairSwapLabel_fixed r hr)
      (fourRowFinitePairSwapLabel_fixed c hc)
  unfold fourRowFiniteSeedPairKey
  rw [fourRowFinitePairLabels_swap r, fourRowFinitePairLabels_swap c]
  have h := fourRowFiniteCanonicalRoleKey_map
    (fourRowFinitePairSwapLabel r) (fourRowFinitePairSwapLabel c)
    (fourRowFinitePairSwapLabel r).injective (fourRowFinitePairSwapLabel c).injective
    (fourRowFiniteSeedMark s)
    ((fourRowFinitePairLabels r).2,(fourRowFinitePairLabels c).2)
    ((fourRowFinitePairLabels r).1,(fourRowFinitePairLabels c).1)
  rw [hm] at h
  exact h.trans (fourRowFiniteCanonicalRoleKey_swap _ _ _)

theorem fourRowFiniteSeedRelationKernel_symm (s : Fin 10) (h : ℕ → ℝ) :
    TwoAxisOrdinarySymm (fourRowFiniteSeedRelationKernel s h) := by
  intro r c
  exact congrArg h (fourRowFiniteSeedPairKey_swap s r c)

end
end DittertRybin
