import DR.Square.FiveMinorTwoBlockProducts
import DR.Square.OrderThreeFinal

/-! The actual size-two and complementary size-three permanent floors,
and their contradiction for the same order-five cut. -/

namespace DittertRybin
open scoped BigOperators
open Certificates.SpectralFiveTwoBlocks

theorem five_two_block_actual_permanent_floors (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2-dittertConstant 5 ≤ dittertFunctional A)
    (I J : Finset (Fin 5)) (hI : I.card = 2) (hJ : J.card = 2)
    (e : I ≃ J) (ec : ↥(Iᶜ) ≃ ↥(Jᶜ)) (horder : LowerMarginalCut A I J)
    (hrL : ∀ i, 79/100 ≤ rowSum A i) (hcL : ∀ j, 79/100 ≤ colSum A j)
    (u v w : ℝ) (hrI : (∑ i ∈ I, rowSum A i) = 2-u)
    (hcJ : (∑ j ∈ J, colSum A j) = 2+v)
    (hw : cutMass A I Jᶜ + cutMass A Iᶜ J = w) (hw1 : w ≤ 13/50) :
    (smallBlockFloorAt u v w-(dittertConstant 5-A.permanent) ≤ (squareCutBlock A I J e).permanent) ∧
    (largeBlockFloorAt u v w-(dittertConstant 5-A.permanent) ≤ (squareCutBlock A Iᶜ Jᶜ ec).permanent) := by
  obtain ⟨hu,hv⟩ := lower_cut_defects_nonneg (by norm_num) A I J horder hmass 2 hI hJ u v hrI hcJ
  have huw := crossing_ge_defect_sum A hA I J 2 u v w 5 hmass hrI hcJ hw
  obtain ⟨_,_,hBmass,hDmass⟩ := cut_block_mass_identities A I J 2 u v w 5 hmass hrI hcJ hw
  obtain ⟨hBR,hBC,hDR,hDC⟩ := five_two_block_actual_products A hA hmass I J hI hJ horder hrL hcL
    u v w hrI hcJ hw hw1
  obtain ⟨hAr,hBc,hCr,hDc⟩ := five_two_block_factor_bounds hu hv huw hw1
  have hR := rowProduct_le_one (by norm_num) A hA hmass
  have hC := colProduct_le_one (by norm_num) A hA hmass
  obtain ⟨_,_,hbudget,_,_⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hsumB := (weighted_factors_shared_deficit hR hC hAr.2 hBc.2 hbudget).trans (add_le_add hBR hBC)
  have hsumD := (weighted_factors_shared_deficit hR hC hCr.2 hDc.2 hbudget).trans (add_le_add hDR hDC)
  have hIc : Iᶜ.card = 3 := by rw [Finset.card_compl,hI]; norm_num
  have hd2 : DittertMaximizer I.card := by rw [hI]; exact dittert_order_two
  have hd3 : DittertMaximizer Iᶜ.card := by rw [hIc]; exact dittert_order_three
  have hperB := hd2.squareCutBlock_lower A hA I J e (by omega)
  have hperD := hd3.squareCutBlock_lower A hA Iᶜ Jᶜ ec (by omega)
  have hg2 : 2-dittertConstant 2 = (3/2:ℝ) := by norm_num [dittertConstant,Nat.factorial]
  have hg3 : 2-dittertConstant 3 = (16/9:ℝ) := by norm_num [dittertConstant,Nat.factorial]
  rw [hI,hg2] at hperB
  rw [hIc,hg3] at hperD
  norm_num only [Nat.cast_ofNat] at hperB hperD
  have hmB : cutMass A I J / 2 = 1+(v-u-w)/4 := by rw [hBmass]; ring
  have hmD : cutMass A Iᶜ Jᶜ / 3 = 1+(u-v-w)/6 := by rw [hDmass]; ring
  rw [hmB] at hperB
  rw [hmD] at hperD
  constructor
  · change fiveSmallRowFactor u v w + fiveSmallColFactor u v w -
      (3/2)*(1+(v-u-w)/4)^2 - (dittertConstant 5-A.permanent) ≤ _
    linarith
  · change fiveLargeRowFactor u v w + fiveLargeColFactor u v w -
      (16/9)*(1+(u-v-w)/6)^3 - (dittertConstant 5-A.permanent) ≤ _
    linarith

/-- No actual contender can possess this ordered balanced size-two cut. -/
theorem five_two_block_cut_contradiction (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2-dittertConstant 5 ≤ dittertFunctional A)
    (I J : Finset (Fin 5)) (hI : I.card = 2) (hJ : J.card = 2)
    (horder : LowerMarginalCut A I J)
    (hrL : ∀ i, 79/100 ≤ rowSum A i) (hcL : ∀ j, 79/100 ≤ colSum A j)
    (hw1 : cutMass A I Jᶜ + cutMass A Iᶜ J ≤ 13/50) : False := by
  let u : ℝ := 2-∑ i ∈ I, rowSum A i
  let v : ℝ := (∑ j ∈ J, colSum A j)-2
  let w := cutMass A I Jᶜ + cutMass A Iᶜ J
  have hrI : (∑ i ∈ I, rowSum A i) = 2-u := by dsimp [u]; ring
  have hcJ : (∑ j ∈ J, colSum A j) = 2+v := by dsimp [v]; ring
  obtain ⟨hu,hv⟩ := lower_cut_defects_nonneg (by norm_num) A I J horder hmass 2 hI hJ u v hrI hcJ
  have huw := crossing_ge_defect_sum A hA I J 2 u v w 5 hmass hrI hcJ rfl
  have hIc : Iᶜ.card = 3 := by rw [Finset.card_compl,hI]; norm_num
  have hJc : Jᶜ.card = 3 := by rw [Finset.card_compl,hJ]; norm_num
  let e : I ≃ J := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hI.trans hJ.symm)
  let ec : ↥(Iᶜ) ≃ ↥(Jᶜ) := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hIc.trans hJc.symm)
  obtain ⟨hB,hD⟩ := five_two_block_actual_permanent_floors A hA hmass hcont I J hI hJ e ec
    horder hrL hcL u v w hrI hcJ rfl hw1
  have hB0 := smallBlockFloor_le_actual hu hv huw hw1
  have hD0 := largeBlockFloor_le_actual hu hv huw hw1
  have hBlo : smallBlockFloor u v-(dittertConstant 5-A.permanent) ≤ (squareCutBlock A I J e).permanent := by
    linarith
  have hDlo : largeBlockFloor u v-(dittertConstant 5-A.permanent) ≤ (squareCutBlock A Iᶜ Jᶜ ec).permanent := by
    linarith
  obtain ⟨_,_,_,hd0,hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hg : dittertConstant 5 = (24/625:ℝ) := by norm_num [dittertConstant,Nat.factorial]
  obtain ⟨hX,hY,hgap⟩ := two_block_floor_gap hu hv (huw.trans hw1) hd0 (hdg.trans_eq hg)
  have hmul := mul_le_mul hBlo hDlo hY.le (hX.le.trans hBlo)
  have hupper := hmul.trans (permanent_squareCutBlocks_le A hA I J e ec)
  rw [hg] at hupper hgap
  linarith

end DittertRybin
