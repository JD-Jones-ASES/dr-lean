import DR.Rectangular.FourRowFiniteCertificate
import DR.Square.OrderFourOrbitNormalization

/-!
# Literal five-cell role keys for the finite four-row families

First-occurrence labels depend only on equality. The first three positions
are the multiplier and the final two are the quadratic pair. Independent
row and column relabelings preserve the key. The numeric radix is 25 for
the five possible labels, irrespective of the physical column count.
-/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFiniteNormalizedKey (cells : List (ℕ × ℕ)) : ℕ :=
  let rows := firstOccurrenceLabels (cells.map Prod.fst)
  let cols := firstOccurrenceLabels (cells.map Prod.snd)
  (rows.zip cols).foldl (fun z p => 25*z + 5*p.1 + p.2) 0

theorem fourRowFiniteNormalizedKey_map (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g) (cells : List (ℕ × ℕ)) :
    fourRowFiniteNormalizedKey (cells.map (Prod.map f g)) = fourRowFiniteNormalizedKey cells := by
  unfold fourRowFiniteNormalizedKey
  have hr : (cells.map (Prod.map f g)).map Prod.fst = (cells.map Prod.fst).map f := by
    simp only [List.map_map, Function.comp_def, Prod.map_fst]
  have hc : (cells.map (Prod.map f g)).map Prod.snd = (cells.map Prod.snd).map g := by
    simp only [List.map_map, Function.comp_def, Prod.map_snd]
  rw [hr, hc, firstOccurrenceLabels_map_injective f hf, firstOccurrenceLabels_map_injective g hg]

def fourRowFiniteCanonicalRoleKey (m : List (ℕ × ℕ)) (a b : ℕ × ℕ) : ℕ :=
  (m.permutations'.flatMap (fun p => [a,b].permutations'.map
    (fun q => fourRowFiniteNormalizedKey (p ++ q)))).foldl min (25^5)

theorem fourRowFiniteCanonicalRoleKey_perm {m m' : List (ℕ × ℕ)}
    (h : m.Perm m') (a b : ℕ × ℕ) :
    fourRowFiniteCanonicalRoleKey m a b = fourRowFiniteCanonicalRoleKey m' a b := by
  unfold fourRowFiniteCanonicalRoleKey
  apply List.Perm.foldl_eq
  exact h.permutations'.flatMap_right _

theorem fourRowFiniteCanonicalRoleKey_swap (m : List (ℕ × ℕ)) (a b : ℕ × ℕ) :
    fourRowFiniteCanonicalRoleKey m a b = fourRowFiniteCanonicalRoleKey m b a := by
  unfold fourRowFiniteCanonicalRoleKey
  apply List.Perm.foldl_eq
  apply List.Perm.flatMap_left
  intro p hp
  exact (List.Perm.swap _ _ []).permutations'.map _

theorem fourRowFiniteCanonicalRoleKey_map (f g : ℕ → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (m : List (ℕ × ℕ)) (a b : ℕ × ℕ) :
    fourRowFiniteCanonicalRoleKey (m.map (Prod.map f g)) (Prod.map f g a) (Prod.map f g b) =
      fourRowFiniteCanonicalRoleKey m a b := by
  unfold fourRowFiniteCanonicalRoleKey
  change (((m.map (Prod.map f g)).permutations'.flatMap
    (fun p => ([a,b].map (Prod.map f g)).permutations'.map
      (fun q => fourRowFiniteNormalizedKey (p ++ q)))).foldl min (25^5)) = _
  simp only [← List.map_permutations', List.flatMap_map, List.map_map]
  congr 1
  apply List.flatMap_congr
  intro p hp
  apply List.map_congr_left
  intro q hq
  simpa only [List.map_append, Function.comp_apply] using
    fourRowFiniteNormalizedKey_map f g hf hg (p ++ q)

def fourRowFiniteExtendLabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : ℕ) : ℕ :=
  if h : a < n then (σ ⟨a,h⟩).val else a

theorem fourRowFiniteExtendLabel_inverse {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : ℕ) :
    fourRowFiniteExtendLabel σ.symm (fourRowFiniteExtendLabel σ a) = a := by
  by_cases h : a < n
  · simp [fourRowFiniteExtendLabel, h, (σ ⟨a,h⟩).isLt]
  · simp [fourRowFiniteExtendLabel, h]

theorem fourRowFiniteExtendLabel_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fourRowFiniteExtendLabel σ) :=
  Function.LeftInverse.injective (fourRowFiniteExtendLabel_inverse σ)

def fourRowFiniteNaturalCell {n : ℕ} (a : FourRowFiniteCell n) : ℕ × ℕ :=
  (a.1.val, a.2.val)

def fourRowFinitePhysicalPermutation {n : ℕ} (r : Equiv.Perm (Fin 4))
    (c : Equiv.Perm (Fin n)) : Equiv.Perm (FourRowFiniteCell n) := Equiv.prodCongr r c

theorem fourRowFiniteNaturalCell_physical {n : ℕ} (r : Equiv.Perm (Fin 4))
    (c : Equiv.Perm (Fin n)) (a : FourRowFiniteCell n) :
    fourRowFiniteNaturalCell (fourRowFinitePhysicalPermutation r c a) =
      Prod.map (fourRowFiniteExtendLabel r) (fourRowFiniteExtendLabel c) (fourRowFiniteNaturalCell a) := by
  simp [fourRowFiniteNaturalCell, fourRowFinitePhysicalPermutation,
    fourRowFiniteExtendLabel, a.1.isLt, a.2.isLt]

/-- The actual full matrix is defined by the role function at its literal multiplier and cells. -/
def fourRowFiniteRoleMatrix {n : ℕ} (coeff : ℕ → ℚ)
    (m : Fin 3 → FourRowFiniteCell n) : Matrix (FourRowFiniteCell n) (FourRowFiniteCell n) ℚ :=
  fun a b => coeff (fourRowFiniteCanonicalRoleKey
    ((List.ofFn m).map fourRowFiniteNaturalCell) (fourRowFiniteNaturalCell a) (fourRowFiniteNaturalCell b))

theorem fourRowFiniteRoleMatrix_symmetric {n : ℕ} (coeff : ℕ → ℚ)
    (m : Fin 3 → FourRowFiniteCell n) : (fourRowFiniteRoleMatrix coeff m).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  exact congrArg coeff (fourRowFiniteCanonicalRoleKey_swap _ _ _)

/-- Physical relabeling conjugates the formula-defined matrix in every dimension. -/
theorem fourRowFiniteRoleMatrix_physical {n : ℕ} (coeff : ℕ → ℚ)
    (m : Fin 3 → FourRowFiniteCell n) (r : Equiv.Perm (Fin 4)) (c : Equiv.Perm (Fin n)) :
    (fourRowFiniteRoleMatrix coeff (fourRowFinitePhysicalPermutation r c ∘ m)).submatrix
      (fourRowFinitePhysicalPermutation r c) (fourRowFinitePhysicalPermutation r c) =
      fourRowFiniteRoleMatrix coeff m := by
  funext a b
  have hm : (List.ofFn (fourRowFinitePhysicalPermutation r c ∘ m)).map fourRowFiniteNaturalCell =
      ((List.ofFn m).map fourRowFiniteNaturalCell).map
        (Prod.map (fourRowFiniteExtendLabel r) (fourRowFiniteExtendLabel c)) := by
    simp only [← List.map_ofFn, List.map_map]
    apply List.map_congr_left
    intro a ha
    exact fourRowFiniteNaturalCell_physical r c a
  change coeff (fourRowFiniteCanonicalRoleKey _ _ _) = coeff (fourRowFiniteCanonicalRoleKey _ _ _)
  rw [hm, fourRowFiniteNaturalCell_physical, fourRowFiniteNaturalCell_physical,
    fourRowFiniteCanonicalRoleKey_map _ _ (fourRowFiniteExtendLabel_injective r)
      (fourRowFiniteExtendLabel_injective c)]

end
end DittertRybin
