import DR.Square.SixSortedCut
import DR.Square.AlternatingSweep

/-!
# The actual order-six alternating cut

The generic alternating path theorem is applied to the sorted stationary
scores of the actual matrix. An odd prefix is unbalanced, while the selected
even prefix has boundary below every unbalanced cut. Complementation by
cardinality retains the singleton extremal orientation.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralSixGuards

/-- The rational alternating threshold is exactly the certified scalar cut bound. -/
theorem six_alternatingBoundary (t : ℝ) :
    alternatingBoundary (sixDominationFactor t) (energy t) (2 / 15) = crossingBound t := by
  unfold alternatingBoundary crossingBound crossingNumerator denominator
  ring

/-- Every nonuniform actual global maximum supplies a balanced cut with the
precise cardinality and singleton orientation needed for the two permanent floors. -/
theorem dittert_globalMax_cut_six (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix 6) :
    ∃ I J : Finset (Fin 6), I.card = J.card ∧ 1 ≤ I.card ∧ I.card ≤ 3 ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        crossingBound (sixDeficitParameter (dittertConstant 6 - A.permanent)) ∧
      (I.card = 1 → ∀ i ∈ I, ∀ j ∈ J,
        ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
        ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) := by
  let e := sixSortedVertices A
  let f := dittertSpectralScore A ∘ e
  let c := fun i j => sixRawConductance A (e i) (e j)
  let t := sixDeficitParameter (dittertConstant 6 - A.permanent)
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht : 0 ≤ t := sixDeficitParameter_nonneg _
  have htcap : t ≤ 31 / 100 := (sixDeficitParameter_le_cap hd0 hdg).le
  have hq : 0 < sixDominationFactor t := by
    have := sixDominationFactor_gt_two_thirds ht htcap
    linarith
  have hh : 0 ≤ energy t := energy_nonneg ht (physical_parameter_sq_le hd0 hdg)
  have hhq : energy t < sixDominationFactor t * (2 / 15) := by
    have := denominator_pos t ht htcap
    unfold denominator at this
    linarith
  obtain ⟨hvar, henergy⟩ := six_sorted_energy_bound A hA hmass hmax hu
  obtain ⟨r, hbound⟩ := exists_even_sweep_prefix_twelve f (sixSortedScore_monotone A) c
    (fun i j => sixRawConductance_nonneg A hA (e i) (e j))
    (fun i j => sixRawConductance_symm A (e i) (e j))
    (sixDominationFactor t) (energy t) hq hh hhq
    (fun j hj => six_odd_prefix_boundary A hA hmass hcont e j
      ⟨j.val / 2, by omega⟩) hvar henergy
  rw [six_alternatingBoundary] at hbound
  let S := (sweepPrefix (evenPrefixIndexTwelve r)).map e.toEmbedding
  have hS : S.Nonempty := Finset.map_nonempty.mpr (sweepPrefix_nonempty _)
  have hproper : S ≠ Finset.univ := by
    intro h
    apply sweepPrefix_ne_univ (evenPrefixIndexTwelve r)
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : e i ∈ S := h ▸ Finset.mem_univ _
    simpa [S] using hi
  apply six_oriented_cut_of_score_prefix A hA hmass hmax S hS hproper
  · change sweepBoundary (sixRawConductance A) S ≤ crossingBound t
    simpa only [c, sweepBoundary_equiv] using hbound
  · exact mapped_sweepPrefix_order e (dittertSpectralScore A) (sixSortedScore_monotone A) _

end DittertRybin
