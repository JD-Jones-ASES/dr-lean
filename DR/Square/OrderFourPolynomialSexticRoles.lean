import DR.Square.OrderFourPolynomialSexticRolesData
import DR.Square.OrderFourPolynomialListCoefficients

/-!
# Sparse sextic role and rational-sum checking interfaces

The role-index gate checks natural canonical keys. The sum gate checks only
the exact rational catalog entries. This avoids recomputing the full
1,484-entry catalog lookup for every term during kernel reduction.
-/

namespace DittertRybin

open Certificates
open scoped BigOperators

set_option maxRecDepth 10000

def orderFourSexticResidualVector (s : Fin 224) (i j : Fin 16) : Vector ℕ 4 :=
  let l := ((orderFourSexticSeedList s).erase i).erase j
  if hl : l.length = 4 then ⟨(l.map Fin.val).toArray, by simpa using hl⟩
  else Vector.replicate 4 0

theorem orderFourSexticResidual_length (s : Fin 224) (i j : Fin 16)
    (hi : i ∈ orderFourSexticSeedList s) (hj : j ∈ (orderFourSexticSeedList s).erase i) :
    (((orderFourSexticSeedList s).erase i).erase j).length = 4 := by
  rw [List.length_erase_of_mem hj, List.length_erase_of_mem hi]
  simp [orderFourSexticSeedList]

noncomputable def orderFourSexticEntryKeyValid (s : Fin 224) : Prop :=
  ∀ i : Fin 16, i ∈ orderFourSexticSeedList s →
    ∀ j : Fin 16, j ∈ (orderFourSexticSeedList s).erase i →
      spectralFourCanonicalRoleKey (orderFourSexticResidualVector s i j) i j =
        spectralFourRoleKeys (orderFourSexticRoleIndex s i j)

noncomputable instance (s : Fin 224) : Decidable (orderFourSexticEntryKeyValid s) :=
  inferInstanceAs (Decidable (∀ i : Fin 16, i ∈ orderFourSexticSeedList s →
    ∀ j : Fin 16, j ∈ (orderFourSexticSeedList s).erase i →
      spectralFourCanonicalRoleKey (orderFourSexticResidualVector s i j) i j =
        spectralFourRoleKeys (orderFourSexticRoleIndex s i j)))

noncomputable def orderFourSexticTableCoefficient (s : Fin 224) : ℚ :=
  ∑ i : Fin 16, if i ∈ orderFourSexticSeedList s then
    ∑ j : Fin 16, if j ∈ (orderFourSexticSeedList s).erase i then
      spectralFourCoefficients (orderFourSexticRoleIndex s i j) else 0 else 0

theorem orderFourSexticListRawMatrix_entry (s : Fin 224) (hkey : orderFourSexticEntryKeyValid s)
    (i j : Fin 16) (hi : i ∈ orderFourSexticSeedList s)
    (hj : j ∈ (orderFourSexticSeedList s).erase i) :
    orderFourListRawMatrix (((orderFourSexticSeedList s).erase i).erase j) i j =
      spectralFourCoefficients (orderFourSexticRoleIndex s i j) := by
  have hl := orderFourSexticResidual_length s i j hi hj
  have h := hkey i hi j hj
  simp only [orderFourSexticResidualVector, dif_pos hl] at h
  rw [orderFourListRawMatrix, dif_pos hl]
  change spectralFourRoleCoefficient (spectralFourCanonicalRoleKey _ i j) = _
  rw [h, spectralFourRoleCoefficient_catalog]

theorem orderFourSexticListCoefficient_eq_table (s : Fin 224)
    (hkey : orderFourSexticEntryKeyValid s) :
    orderFourCertificateListCoefficient (orderFourSexticSeedList s) =
      orderFourSexticTableCoefficient s := by
  unfold orderFourCertificateListCoefficient orderFourSexticTableCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with his
  · apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hjs
    · exact orderFourSexticListRawMatrix_entry s hkey i j his hjs
    · rfl
  · rfl

end DittertRybin
