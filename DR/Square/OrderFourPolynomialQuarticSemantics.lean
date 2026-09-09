import DR.Square.OrderFourPolynomialQuarticCheck
import DR.Square.OrderFourPolynomialCoefficientSymmetry

namespace DittertRybin

open Certificates MvPolynomial

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem orderFourQuarticSeedList_val (s : Fin 33) :
    (orderFourQuarticSeedList s : Multiset (Fin 16)).map Fin.val =
      ((spectralFourMultipliers.get s).toList : Multiset ℕ) := by
  have hb : ∀ t : Fin 33,
      (spectralFourMultipliers.get t).toList.all (fun a => decide (a < 16)) = true := by
    decide +kernel
  have hbound (a : ℕ) (ha : a ∈ (spectralFourMultipliers.get s).toList) : a < 16 := by
    simpa only [decide_eq_true_eq] using List.all_eq_true.mp (hb s) a ha
  simp only [orderFourQuarticSeedList, Multiset.map_coe, List.map_map]
  congr 1
  calc
    _ = (spectralFourMultipliers.get s).toList.map id :=
      List.map_congr_left (fun a ha => Nat.mod_eq_of_lt (hbound a ha))
    _ = _ := List.map_id _

theorem orderFourQuarticSeedCells_physical_val (s : Fin 33)
    (r c : Equiv.Perm (Fin 4)) :
    (((orderFourQuarticSeedList s : Multiset (Fin 16)).map
      (orderFourPhysicalPermutation r c)).map Fin.val) =
      (((spectralFourMultipliers.get s).map (orderFourCellMapNat r c)).toList : Multiset ℕ) := by
  rw [Multiset.map_map]
  change (orderFourQuarticSeedList s : Multiset (Fin 16)).map
    (orderFourCellMapNat r c ∘ Fin.val) = _
  rw [← Multiset.map_map, orderFourQuarticSeedList_val]
  simp only [Multiset.map_coe, Vector.toList_map]

theorem orderFourQuartic_multiset_orbit (s : Multiset (Fin 16)) (hs : s.card = 4) :
    ∃ (t : Fin 33) (r c : Equiv.Perm (Fin 4)),
      (orderFourQuarticSeedList t : Multiset (Fin 16)).map
        (orderFourPhysicalPermutation r c) = s := by
  obtain ⟨t,r,c,h⟩ := orderFourSortedMultiplier_orbit (⟨s,hs⟩ : Sym (Fin 16) 4)
  refine ⟨t,r,c,?_⟩
  apply Multiset.map_injective Fin.val_injective
  rw [orderFourQuarticSeedCells_physical_val]
  have he := Multiset.coe_eq_coe.mpr h
  simpa only [orderFourSortedMultiplier_toList, ← Multiset.map_coe, Multiset.sort_eq] using he

def orderFourQuarticSuccess (s : Multiset (Fin 16)) : Prop :=
  (s.map (fun a => a.val / 4)).Nodup ∨ (s.map (fun a => a.val % 4)).Nodup

instance (s : Multiset (Fin 16)) : Decidable (orderFourQuarticSuccess s) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem orderFourQuarticSuccess_physical (s : Multiset (Fin 16))
    (r c : Equiv.Perm (Fin 4)) :
    orderFourQuarticSuccess (s.map (orderFourPhysicalPermutation r c)) ↔
      orderFourQuarticSuccess s := by
  have hr : (s.map (orderFourPhysicalPermutation r c)).map (fun a => a.val / 4) =
      (s.map (fun a => a.val / 4)).map (orderFourExtendLabel r) := by
    simp only [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a ha
    exact orderFourCellMapNat_div r c a.val
  have hc : (s.map (orderFourPhysicalPermutation r c)).map (fun a => a.val % 4) =
      (s.map (fun a => a.val % 4)).map (orderFourExtendLabel c) := by
    simp only [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a ha
    exact orderFourCellMapNat_mod r c a.val
  unfold orderFourQuarticSuccess
  rw [hr,hc, Multiset.nodup_map_iff_of_injective (orderFourExtendLabel_injective r),
    Multiset.nodup_map_iff_of_injective (orderFourExtendLabel_injective c)]

theorem orderFourQuarticPolynomial_coeff_four (s : Multiset (Fin 16)) (hs : s.card = 4) :
    coeff s.toFinsupp orderFourQuarticPolynomial =
      if orderFourQuarticSuccess s then (24:ℚ) else 0 := by
  obtain ⟨t,r,c,ht⟩ := orderFourQuartic_multiset_orbit s hs
  rw [← ht, orderFour_coeff_physical _ r c (orderFourQuarticPolynomial_rename r c)]
  simp only [orderFourQuarticSuccess_physical]
  simpa only [orderFourQuarticSuccess, Multiset.map_coe, Multiset.coe_nodup,
    orderFourQuarticListSuccess] using orderFourQuarticCoefficient_seed t

theorem orderFourQuarticPolynomial_coeff_multiset (s : Multiset (Fin 16)) :
    coeff s.toFinsupp orderFourQuarticPolynomial =
      if s.card = 4 ∧ orderFourQuarticSuccess s then (24:ℚ) else 0 := by
  by_cases hs : s.card = 4
  · rw [orderFourQuarticPolynomial_coeff_four s hs]
    simp only [hs, true_and]
  · rw [orderFourQuarticPolynomial_isHomogeneous.coeff_eq_zero
      (by simpa only [orderFour_toFinsupp_degree] using hs)]
    simp only [hs, false_and, if_false]

end DittertRybin
