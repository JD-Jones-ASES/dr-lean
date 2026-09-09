import DR.Square.SpectralCut
import DR.Certificates.SpectralFiveGuards

/-! Actual transport and unbalanced-cut bounds for order five. -/

namespace DittertRybin
open scoped BigOperators
open Certificates.SpectralFiveGuards

theorem five_contender_transportCuts (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2 - dittertConstant 5 ≤ dittertFunctional A) :
    TransportCuts A (domination (fiveDeficitParameter (dittertConstant 5 - A.permanent))) := by
  obtain ⟨_, _, _, hd0, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht := fiveDeficitParameter_nonneg (dittertConstant 5 - A.permanent)
  have ht1 := fiveDeficitParameter_lt_cap hd0 hdg
  exact transportCuts_of_shared_discrepancy A hA hmass _ ht (by linarith)
    (dittert_contender_subset_discrepancy (by norm_num) A hA hmass hcont)

theorem five_contender_dominated_doublyStochastic (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2 - dittertConstant 5 ≤ dittertFunctional A) :
    ∃ B ∈ doublyStochastic ℝ (Fin 5), ∀ i j,
      domination (fiveDeficitParameter (dittertConstant 5 - A.permanent)) * B i j ≤ A i j := by
  obtain ⟨_, _, _, hd0, hdg⟩ :=
    dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht1 := fiveDeficitParameter_lt_cap hd0 hdg
  apply exists_doublyStochastic_dominated_of_cuts hA
  · unfold domination; linarith
  · exact five_contender_transportCuts A hA hmass hcont

theorem five_contender_unbalanced_crossing (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2 - dittertConstant 5 ≤ dittertFunctional A)
    (I J : Finset (Fin 5)) (hcard : I.card ≠ J.card) :
    domination (fiveDeficitParameter (dittertConstant 5 - A.permanent)) ≤
      cutMass A I Jᶜ + cutMass A Iᶜ J := by
  have hdisc := dittert_contender_subset_discrepancy (by norm_num) A hA hmass hcont I J
  have hrows := cutMass_add_compl_cols A I J
  have hcols := cutMass_add_compl_rows A I J
  have hleft := cutMass_nonneg hA I Jᶜ
  have hright := cutMass_nonneg hA Iᶜ J
  have hi₁ := le_abs_self ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hi₂ := neg_abs_le ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hj₁ := le_abs_self ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  have hj₂ := neg_abs_le ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  change _ ≤ fiveDeficitParameter (dittertConstant 5 - A.permanent) at hdisc
  unfold domination
  rcases lt_or_gt_of_ne hcard with hlt | hgt
  · have hcast : (I.card : ℝ) + 1 ≤ J.card := by exact_mod_cast hlt
    linarith
  · have hcast : (J.card : ℝ) + 1 ≤ I.card := by exact_mod_cast hgt
    linarith

end DittertRybin
