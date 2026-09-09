import DR.Square.OrderFourOrbitAugmentedCoverage
import DR.Square.OrderFourPolynomialSexticData
import DR.Square.OrderFourPolynomialCoefficientSymmetry
import DR.Square.OrderFourPolynomialQuarticSemantics

/-!
# Transfer from the 224 checked sextic representatives

The witness coverage is converted to a statement about actual multisets of
physical cells. Polynomial coefficients then transfer by the proved physical
rename invariance, using Mathlib's injective-renaming coefficient theorem.
-/

namespace DittertRybin

open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem orderFourSexticSeeds_bounds (s : Fin 224) (a : ℕ)
    (ha : a ∈ (orderFourSexticSeeds.get s).toList) : a < 16 := by
  have h : ∀ s : Fin 224,
      (orderFourSexticSeeds.get s).toList.all (fun a => decide (a < 16)) = true := by
    decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp (h s) a ha

theorem orderFourSexticSeedCells_val (s : Fin 224) :
    (orderFourSexticSeedCells s).map Fin.val =
      ((orderFourSexticSeeds.get s).toList : Multiset ℕ) := by
  simp only [orderFourSexticSeedCells, orderFourSexticSeedList, Multiset.map_coe, List.map_map]
  congr 1
  calc
    _ = (orderFourSexticSeeds.get s).toList.map id :=
      List.map_congr_left (fun a ha => Nat.mod_eq_of_lt (orderFourSexticSeeds_bounds s a ha))
    _ = _ := List.map_id _

theorem orderFourSexticSeedCells_physical_val (s : Fin 224)
    (r c : Equiv.Perm (Fin 4)) :
    ((orderFourSexticSeedCells s).map (orderFourPhysicalPermutation r c)).map Fin.val =
      (((orderFourSexticSeeds.get s).map (orderFourCellMapNat r c)).toList : Multiset ℕ) := by
  rw [Multiset.map_map]
  change (orderFourSexticSeedCells s).map (orderFourCellMapNat r c ∘ Fin.val) = _
  rw [← Multiset.map_map, orderFourSexticSeedCells_val]
  simp only [Multiset.map_coe, Vector.toList_map]

theorem orderFourAugmented_multiset_orbit (t : Fin 33) (i j : Fin 16) :
    ∃ (u : Fin 224) (r c : Equiv.Perm (Fin 4)),
      (orderFourSexticSeedCells u).map (orderFourPhysicalPermutation r c) =
        (orderFourQuarticSeedList t : Multiset (Fin 16)) + (i ::ₘ j ::ₘ 0) := by
  let w := orderFourAugmentedWitness t i j
  refine ⟨w.1, orderFourLabelPermutation w.2.1, orderFourLabelPermutation w.2.2, ?_⟩
  apply Multiset.map_injective Fin.val_injective
  rw [orderFourSexticSeedCells_physical_val, Multiset.map_add, orderFourQuarticSeedList_val]
  exact Multiset.coe_eq_coe.mpr (orderFourAugmentedCoverage t i j)

theorem orderFourPhysicalPermutation_trans (r₁ r₂ c₁ c₂ : Equiv.Perm (Fin 4)) :
    orderFourPhysicalPermutation (r₁.trans r₂) (c₁.trans c₂) =
      (orderFourPhysicalPermutation r₁ c₁).trans (orderFourPhysicalPermutation r₂ c₂) := by
  apply Equiv.ext
  intro a
  obtain ⟨⟨i,j⟩,rfl⟩ := orderFourCell.surjective a
  simp only [Equiv.trans_apply, orderFourPhysicalPermutation_cell]

/-- Every six-cell multiset reduces first through four-cell coverage and then
through one of the 8,448 augmented-seed cases. -/
theorem orderFourSextic_multiset_orbit (s : Multiset (Fin 16)) (hs : s.card = 6) :
    ∃ (t : Fin 224) (r c : Equiv.Perm (Fin 4)),
      (orderFourSexticSeedCells t).map (orderFourPhysicalPermutation r c) = s := by
  obtain ⟨i,hi⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < s.card by omega)
  have h5 : (s.erase i).card = 5 := by simp only [Multiset.card_erase_of_mem hi, hs]; rfl
  obtain ⟨j,hj⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < (s.erase i).card by omega)
  have h4 : ((s.erase i).erase j).card = 4 := by simp only [Multiset.card_erase_of_mem hj, h5]; rfl
  obtain ⟨t,r,c,ht⟩ := orderFourQuartic_multiset_orbit _ h4
  let e := orderFourPhysicalPermutation r c
  obtain ⟨u,r',c',hu⟩ := orderFourAugmented_multiset_orbit t (e.symm i) (e.symm j)
  refine ⟨u,r'.trans r,c'.trans c,?_⟩
  rw [orderFourPhysicalPermutation_trans]
  change (orderFourSexticSeedCells u).map (e ∘ orderFourPhysicalPermutation r' c') = s
  rw [← Multiset.map_map, hu, Multiset.map_add]
  change (orderFourQuarticSeedList t : Multiset (Fin 16)).map
    (orderFourPhysicalPermutation r c) + ((e.symm i ::ₘ e.symm j ::ₘ 0).map e) = s
  rw [ht]
  simp only [Multiset.map_cons, Multiset.map_zero, Equiv.apply_symm_apply,
    Multiset.add_cons, Multiset.add_zero]
  rw [Multiset.cons_erase hj, Multiset.cons_erase hi]

end DittertRybin
