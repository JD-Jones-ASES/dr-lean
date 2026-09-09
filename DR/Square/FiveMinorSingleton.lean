import DR.Square.FiveMinorSingletonProducts
import DR.Square.SixMatrixBounds

/-! The actual four-by-four deletion minor, conditional only on the independent
order-four Dittert theorem. No singleton scalar gap is assumed here. -/

namespace DittertRybin
open scoped BigOperators
open Certificates.SpectralFiveSingleton

theorem five_singleton_actual_minor_floor (h4 : DittertMaximizer 4)
    (A : Board 5 5) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2-dittertConstant 5 ≤ dittertFunctional A)
    (i j : Fin 5) (a b L w : ℝ) (haEq : rowSum A i = a) (hbEq : colSum A j = b)
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 793/1000 ≤ L) (hrow : ∀ r, a ≤ rowSum A r) (hcol : ∀ c, L ≤ colSum A c)
    (hw : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} = w) (hw1 : w ≤ 13/50)
    (ec : ↥({i}ᶜ : Finset (Fin 5)) ≃ ↥({j}ᶜ : Finset (Fin 5))) :
    singletonMinorFloor a b L (dittertConstant 5-A.permanent) w ≤
      (squareCutBlock A {i}ᶜ {j}ᶜ ec).permanent := by
  have hrI : (∑ r ∈ ({i}:Finset (Fin 5)), rowSum A r) = 1-(1-a) := by simp [haEq]
  have hcJ : (∑ c ∈ ({j}:Finset (Fin 5)), colSum A c) = 1+(b-1) := by simp [hbEq]
  have huw := crossing_ge_defect_sum A hA {i} {j} 1 (1-a) (b-1) w 5 hmass hrI hcJ hw
  obtain ⟨_,_,_,hM⟩ := cut_block_mass_identities A {i} {j} 1 (1-a) (b-1) w 5 hmass hrI hcJ hw
  obtain ⟨hRP,hCP⟩ := five_singleton_actual_products A hA i j a b L w haEq hbEq
    ha ha1 hb hb1 hL hrow hcol hw hw1
  obtain ⟨hAr,hBc⟩ := five_singleton_factor_bounds ha ha1 hb hb1 hL (by linarith) hw1
  have hR := rowProduct_le_one (by norm_num) A hA hmass
  have hC := colProduct_le_one (by norm_num) A hA hmass
  obtain ⟨_,_,hbudget,_,_⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hsum := (weighted_factors_shared_deficit hR hC hAr.2 hBc.2 hbudget).trans (add_le_add hRP hCP)
  have hIc : ({i}ᶜ : Finset (Fin 5)).card = 4 := by simp [Finset.card_compl]
  have hd4 : DittertMaximizer ({i}ᶜ : Finset (Fin 5)).card := by rw [hIc]; exact h4
  have hper := hd4.squareCutBlock_lower A hA {i}ᶜ {j}ᶜ ec (by omega)
  have hg4 : 2-dittertConstant 4 = (61/32:ℝ) := by norm_num [dittertConstant,Nat.factorial]
  rw [hIc,hg4] at hper
  norm_num only [Nat.cast_ofNat] at hper
  have hmean : cutMass A {i}ᶜ {j}ᶜ / 4 = (10-a-b-w)/8 := by rw [hM]; ring
  rw [hmean] at hper
  change fiveSingletonRowFactor a b w + fiveSingletonColFactor a b L w -
    (dittertConstant 5-A.permanent) - (61/32)*((10-a-b-w)/8)^4 ≤ _
  linarith

/-- The distinguished actual entry multiplies the actual minor lower bound. -/
theorem five_singleton_actual_permanent_lower (h4 : DittertMaximizer 4)
    (A : Board 5 5) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2-dittertConstant 5 ≤ dittertFunctional A)
    (i j : Fin 5) (a b L w : ℝ) (haEq : rowSum A i = a) (hbEq : colSum A j = b)
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 793/1000 ≤ L) (hrow : ∀ r, a ≤ rowSum A r) (hcol : ∀ c, L ≤ colSum A c)
    (hw : cutMass A {i} {j}ᶜ + cutMass A {i}ᶜ {j} = w) (hw1 : w ≤ 13/50) :
    singletonEntry a b w * singletonMinorFloor a b L (dittertConstant 5-A.permanent) w ≤ A.permanent := by
  let e : ({i}:Finset (Fin 5)) ≃ ({j}:Finset (Fin 5)) := Fintype.equivOfCardEq (by simp)
  let ec : ↥({i}ᶜ : Finset (Fin 5)) ≃ ↥({j}ᶜ : Finset (Fin 5)) :=
    Fintype.equivOfCardEq (by simp)
  have hminor := five_singleton_actual_minor_floor h4 A hA hmass hcont i j a b L w
    haEq hbEq ha ha1 hb hb1 hL hrow hcol hw hw1 ec
  have hrI : (∑ r ∈ ({i}:Finset (Fin 5)), rowSum A r) = 1-(1-a) := by simp [haEq]
  have hcJ : (∑ c ∈ ({j}:Finset (Fin 5)), colSum A c) = 1+(b-1) := by simp [hbEq]
  have hentry := (cut_block_mass_identities A {i} {j} 1 (1-a) (b-1) w 5 hmass hrI hcJ hw).2.2.1
  simp only [cutMass, Finset.sum_singleton] at hentry
  have heq : singletonEntry a b w = A i j := by unfold singletonEntry; linarith
  have hkeep := permanent_squareCutBlocks_le A hA {i} {j} e ec
  rw [permanent_singleton_squareCutBlock] at hkeep
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hminor (hA i j)).trans hkeep

end DittertRybin
