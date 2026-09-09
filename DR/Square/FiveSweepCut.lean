import DR.Square.FiveSortedCut
import DR.Square.AlternatingSweepTen

/-!
# The actual order-five alternating cut

The generic alternating path theorem is applied to the sorted stationary
scores of the actual matrix. An odd prefix is unbalanced, while the selected
even prefix has boundary below every unbalanced cut. Complementation by
cardinality retains the singleton extremal orientation.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralFiveGuards

/-- The rational alternating threshold is exactly the certified scalar cut bound. -/
theorem five_alternatingBoundary (t : ℝ) :
    alternatingBoundary (domination t) (energy t) (19 / 100) = crossingBound t := by
  unfold alternatingBoundary crossingBound crossingNumerator denominator
  ring

/-- Every nonuniform actual global maximum supplies a balanced cut with the
precise cardinality and singleton orientation needed for the two permanent floors. -/
theorem dittert_globalMax_cut_five (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix 5) :
    ∃ I J : Finset (Fin 5), I.card = J.card ∧ 1 ≤ I.card ∧ I.card ≤ 2 ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        crossingBound (fiveDeficitParameter (dittertConstant 5 - A.permanent)) ∧
      (LowerMarginalCut A I J ∨ LowerMarginalCut A.transpose J I) ∧
      (((∑ i ∈ I, rowSum A i) ≤ I.card ∧ (J.card : ℝ) ≤ ∑ j ∈ J, colSum A j) ∨
        ((I.card : ℝ) ≤ (∑ i ∈ I, rowSum A i) ∧ (∑ j ∈ J, colSum A j) ≤ J.card)) ∧
      (I.card = 1 → ∀ i ∈ I, ∀ j ∈ J,
        ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
        ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) := by
  let e := fiveSortedVertices A
  let f := dittertSpectralScore A ∘ e
  let c := fun i j => fiveRawConductance A (e i) (e j)
  let t := fiveDeficitParameter (dittertConstant 5 - A.permanent)
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have ht : 0 ≤ t := fiveDeficitParameter_nonneg _
  have htcap : t ≤ 9 / 20 := (fiveDeficitParameter_lt_cap hd0 hdg).le
  have hq : 0 < domination t := by
    have := domination_ge_eleven_twentieths htcap
    linarith
  have hh : 0 ≤ energy t := energy_nonneg ht (physical_parameter_sq_le hd0 hdg)
  have hhq : energy t < domination t * (19 / 100) := by
    have := denominator_pos t ht htcap
    unfold denominator at this
    linarith
  obtain ⟨hvar, henergy⟩ := five_sorted_energy_bound A hA hmass hmax hu
  obtain ⟨r, hbound⟩ := exists_even_sweep_prefix_ten f (fiveSortedScore_monotone A) c
    (fun i j => fiveRawConductance_nonneg A hA (e i) (e j))
    (fun i j => fiveRawConductance_symm A (e i) (e j))
    (domination t) (energy t) hq hh hhq
    (fun j hj => five_odd_prefix_boundary A hA hmass hcont e j
      ⟨j.val / 2, by omega⟩) hvar henergy
  rw [five_alternatingBoundary] at hbound
  let S := (sweepPrefix (evenPrefixIndexTen r)).map e.toEmbedding
  have hS : S.Nonempty := Finset.map_nonempty.mpr (sweepPrefix_nonempty _)
  have hproper : S ≠ Finset.univ := by
    intro h
    apply sweepPrefix_ne_univ (evenPrefixIndexTen r)
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : e i ∈ S := h ▸ Finset.mem_univ _
    simpa [S] using hi
  apply five_oriented_cut_of_score_prefix A hA hmass hmax S hS hproper
  · change sweepBoundary (fiveRawConductance A) S ≤ crossingBound t
    simpa only [c, sweepBoundary_equiv] using hbound
  · exact mapped_sweepPrefix_order e (dittertSpectralScore A) (fiveSortedScore_monotone A) _

end DittertRybin
