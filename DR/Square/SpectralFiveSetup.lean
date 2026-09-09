import DR.Square.FiveSweepCut
import DR.Square.FiveMinorTwoBlocks
import DR.Square.FiveMinorSingleton
import DR.Certificates.SpectralFiveSingletonCoordinates

/-! Actual global-maximizer consequences used by the final order-five assembly. -/

namespace DittertRybin
open scoped BigOperators
open Certificates.SpectralFiveGuards

theorem five_globalMax_coarse_marginal_floor (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) :
    (∀ i, 79/100 ≤ rowSum A i) ∧ (∀ j, 79/100 ≤ colSum A j) := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_,_,_,hd0,hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht := fiveDeficitParameter_lt_cap hd0 hdg
  obtain ⟨hr,hc⟩ := five_globalMax_marginal_bounds A hA hmass hmax
  constructor
  · intro i; linarith [(hr i).1]
  · intro j; linarith [(hc j).1]

theorem five_extremal_marginals_straddle_one (A : Board 5 5)
    (hmass : totalMass A = 5) (i j : Fin 5)
    (hrow : ∀ r, rowSum A i ≤ rowSum A r) (hcol : ∀ c, colSum A c ≤ colSum A j) :
    rowSum A i ≤ 1 ∧ 1 ≤ colSum A j := by
  have hr := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hrow r
  have hc := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hcol c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr hc
  change (5:ℝ)*rowSum A i ≤ totalMass A at hr
  rw [hmass] at hr
  rw [← totalMass_eq_sum_colSum,hmass] at hc
  norm_num only [Nat.cast_ofNat] at hc
  constructor <;> linarith

/-- Either retained marginal orientation of an actual size-two cut is impossible. -/
theorem five_globalMax_two_cut_contradiction (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A)
    (I J : Finset (Fin 5)) (hI : I.card = 2) (hJ : J.card = 2)
    (horder : LowerMarginalCut A I J ∨ LowerMarginalCut A.transpose J I)
    (hw : cutMass A I Jᶜ + cutMass A Iᶜ J ≤
      crossingBound (fiveDeficitParameter (dittertConstant 5-A.permanent))) : False := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_,_,_,hd0,hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht := fiveDeficitParameter_nonneg (dittertConstant 5-A.permanent)
  have ht1 := (fiveDeficitParameter_lt_cap hd0 hdg).le
  have hw1 := hw.trans (crossingBound_lt_thirteen_fiftieths _ ht ht1).le
  obtain ⟨hrL,hcL⟩ := five_globalMax_coarse_marginal_floor A hA hmass hmax
  rcases horder with horder | horder
  · exact five_two_block_cut_contradiction A hA hmass hcont I J hI hJ horder hrL hcL hw1
  · have hmassT : totalMass A.transpose = 5 := (totalMass_matrix_transpose A).trans hmass
    have hcontT : 2-dittertConstant 5 ≤ dittertFunctional A.transpose := by
      rwa [dittertFunctional_transpose]
    apply five_two_block_cut_contradiction A.transpose (fun i j => hA j i) hmassT hcontT
      J I hJ hI horder hcL hrL
    simpa only [cutMass_transpose_eq, add_comm] using hw1

end DittertRybin
