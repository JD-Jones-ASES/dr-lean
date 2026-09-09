import DR.Square.OrderFourOrbitNormalization

/-!
# Physical and role symmetries of the order-four quadratic matrices

These are semantic consequences of the formula defining each matrix entry.
The catalog lookup and its positive semidefinite seed checks are not used to
infer invariance.
-/

namespace DittertRybin

open Certificates

set_option maxRecDepth 10000

theorem spectralFourCanonicalRoleKey_perm {m m' : Vector ℕ 4}
    (hm : m.toList.Perm m'.toList) (i j : Fin 16) :
    spectralFourCanonicalRoleKey m i j = spectralFourCanonicalRoleKey m' i j := by
  unfold spectralFourCanonicalRoleKey
  apply List.Perm.foldl_eq
  exact hm.permutations'.flatMap_right _

theorem spectralFourCanonicalRoleKey_swap (m : Vector ℕ 4) (i j : Fin 16) :
    spectralFourCanonicalRoleKey m i j = spectralFourCanonicalRoleKey m j i := by
  unfold spectralFourCanonicalRoleKey
  apply List.Perm.foldl_eq
  apply List.Perm.flatMap_left
  intro a ha
  exact (List.Perm.swap _ _ []).permutations'.map _

theorem spectralFourCanonicalRoleKey_physical
    (r c : Equiv.Perm (Fin 4)) (m : Vector ℕ 4) (i j : Fin 16) :
    spectralFourCanonicalRoleKey (m.map (orderFourCellMapNat r c))
      (orderFourPhysicalPermutation r c i) (orderFourPhysicalPermutation r c j) =
      spectralFourCanonicalRoleKey m i j := by
  unfold spectralFourCanonicalRoleKey
  simp only [Vector.toList_map]
  change (((m.toList.map (orderFourCellMapNat r c)).permutations'.flatMap
    (fun a => ([i.val, j.val].map (orderFourCellMapNat r c)).permutations'.map
      (fun q => spectralFourNormalizedKey (a ++ q)))).foldl min (16 ^ 6)) = _
  simp only [← List.map_permutations', List.flatMap_map, List.map_map]
  congr 1
  apply List.flatMap_congr
  intro a ha
  apply List.map_congr_left
  intro q hq
  simpa only [List.map_append, Function.comp_apply] using
    spectralFourNormalizedKey_physical r c (a ++ q)

/-- A formula-defined matrix for any four multiplier cells. -/
noncomputable def orderFourMultiplierMatrix (m : Vector ℕ 4) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => spectralFourRoleCoefficient (spectralFourCanonicalRoleKey m i j)

theorem orderFourMultiplierMatrix_seed (s : Fin 33) :
    orderFourMultiplierMatrix (spectralFourMultipliers.get s) = spectralFourSeedMatrix s := rfl

theorem orderFourMultiplierMatrix_perm {m m' : Vector ℕ 4}
    (hm : m.toList.Perm m'.toList) :
    orderFourMultiplierMatrix m = orderFourMultiplierMatrix m' := by
  funext i j
  simp only [orderFourMultiplierMatrix, spectralFourCanonicalRoleKey_perm hm]

theorem orderFourMultiplierMatrix_symmetric (m : Vector ℕ 4) :
    (orderFourMultiplierMatrix m).IsSymm := by
  change (orderFourMultiplierMatrix m).transpose = orderFourMultiplierMatrix m
  funext i j
  change spectralFourRoleCoefficient (spectralFourCanonicalRoleKey m j i) =
    spectralFourRoleCoefficient (spectralFourCanonicalRoleKey m i j)
  exact congrArg spectralFourRoleCoefficient (spectralFourCanonicalRoleKey_swap m j i)

/-- Independent row and column permutations conjugate the full physical matrix. -/
theorem orderFourMultiplierMatrix_physical
    (r c : Equiv.Perm (Fin 4)) (m : Vector ℕ 4) :
    (orderFourMultiplierMatrix (m.map (orderFourCellMapNat r c))).submatrix
      (orderFourPhysicalPermutation r c) (orderFourPhysicalPermutation r c) =
      orderFourMultiplierMatrix m := by
  funext i j
  change spectralFourRoleCoefficient (spectralFourCanonicalRoleKey
    (m.map (orderFourCellMapNat r c)) (orderFourPhysicalPermutation r c i)
      (orderFourPhysicalPermutation r c j)) =
    spectralFourRoleCoefficient (spectralFourCanonicalRoleKey m i j)
  exact congrArg spectralFourRoleCoefficient
    (spectralFourCanonicalRoleKey_physical r c m i j)

end DittertRybin
