import DR.Square.FiveMatrixBounds
import DR.Square.MarginalCutOrder
import DR.Square.SixSortedCut
import DR.Square.RefinedSweep
import Mathlib.Order.Interval.Finset.Fin

/-!
# Actual sorted score and raw conductance at order five

These identities prepare the alternating sweep on the actual ten matrix
vertices. Conductance is unnormalized here, so its cut boundary is exactly
the sum of the two off-diagonal matrix rectangles.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralFiveGuards

noncomputable def fiveSortedVertices (A : Board 5 5) : Fin 10 ≃ SquareVertices 5 :=
  let e : Fin 10 ≃ SquareVertices 5 := (Fintype.equivFin (SquareVertices 5)).symm
  (Tuple.sort (dittertSpectralScore A ∘ e)).trans e

noncomputable def fiveRawConductance (A : Board 5 5) (v w : SquareVertices 5) : ℝ :=
  10 * squareConductance A v w

theorem fiveSortedScore_monotone (A : Board 5 5) :
    Monotone (dittertSpectralScore A ∘ fiveSortedVertices A) := by
  exact Tuple.monotone_sort
    (dittertSpectralScore A ∘ (Fintype.equivFin (SquareVertices 5)).symm)

theorem fiveRawConductance_nonneg (A : Board 5 5) (hA : ∀ i j, 0 ≤ A i j)
    (v w : SquareVertices 5) : 0 ≤ fiveRawConductance A v w :=
  mul_nonneg (by norm_num) (squareConductance_nonneg A hA v w)

theorem fiveRawConductance_symm (A : Board 5 5) (v w : SquareVertices 5) :
    fiveRawConductance A v w = fiveRawConductance A w v := by
  unfold fiveRawConductance
  rw [squareConductance_symm A v w]

theorem fiveRawEnergy (A : Board 5 5) (f : SquareVertices 5 → ℝ) :
    sweepEnergy (fiveRawConductance A) f = 10 * sweepEnergy (squareConductance A) f := by
  simp only [sweepEnergy, fiveRawConductance, mul_assoc, ← Finset.mul_sum]
  ring

theorem fiveRawBoundary (A : Board 5 5) (S : Finset (SquareVertices 5)) :
    sweepBoundary (fiveRawConductance A) S =
      cutMass A S.toLeft S.toRightᶜ + cutMass A S.toLeftᶜ S.toRight := by
  have heq : sweepBoundary (fiveRawConductance A) S = 10 * sweepBoundary (squareConductance A) S := by
    simp only [sweepBoundary, fiveRawConductance, Finset.mul_sum]
  rw [heq, squareSweepBoundary]
  norm_num
  ring

/-- The actual sorted stationary score has positive unweighted variance and
satisfies the raw energy bound needed by the alternating path. -/
theorem five_sorted_energy_bound (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix 5) :
    let e := fiveSortedVertices A
    let f := dittertSpectralScore A ∘ e
    let U := ∑ i, (f i - (∑ j, f j) / 10) ^ 2
    0 < U ∧
      sweepEnergy (fun i j => fiveRawConductance A (e i) (e j)) f ≤
        energy (fiveDeficitParameter (dittertConstant 5 - A.permanent)) * U := by
  dsimp only
  let e := fiveSortedVertices A
  let f := dittertSpectralScore A ∘ e
  let π := squareVertexWeight A ∘ e
  let t := fiveDeficitParameter (dittertConstant 5 - A.permanent)
  let U := ∑ i, (f i - (∑ j, f j) / 10) ^ 2
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have ht : 0 ≤ t := fiveDeficitParameter_nonneg _
  have hH : 0 < height t := by unfold height; linarith
  obtain ⟨hrcap, hccap⟩ := five_globalMax_marginal_bounds A hA hmass hmax
  have hπsum : ∑ i, π i = 1 := (Equiv.sum_comp e _).trans (squareVertexWeight_sum (by norm_num) A hmass)
  have hπcap (i : Fin 10) : π i ≤ height t / 10 := by
    dsimp [π, Function.comp_def]
    cases e i with
    | inl r => dsimp [squareVertexWeight, height, t]; linarith [(hrcap r).2]
    | inr c => dsimp [squareVertexWeight, height, t]; linarith [(hccap c).2]
  have hVcap : sweepVariance π f ≤ height t / 10 * U :=
    sweepVariance_le_cap_centered π f hπsum _ hπcap
  have hV : 0 < sweepVariance π f := by
    dsimp only [π, f]
    rw [sweepVariance_equiv]
    exact dittert_globalMax_variance_pos (by norm_num) A hA hmass hmax hu
  have hU : 0 < U := by
    by_contra! hU
    have hnon := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ height t / 10) hU
    linarith
  refine ⟨hU, ?_⟩
  have hgap := dittert_globalMax_gap_bounds (by norm_num) A hA hmass hmax hu
  have hE : sweepEnergy (fun i j => fiveRawConductance A (e i) (e j)) f =
      10 * dittertSpectralGap A * sweepVariance π f := by
    dsimp only [f, π]
    rw [sweepEnergy_equiv, fiveRawEnergy, dittert_globalMax_energy (by norm_num) A hA hmass hmax,
      sweepVariance_equiv]
    ring
  have hraw := mul_le_mul_of_nonneg_left hVcap (by linarith : 0 ≤ 10 * dittertSpectralGap A)
  have hupper := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap.2 hH.le) hU.le
  have henergy : energy t = height t * A.permanent / (1 - (dittertConstant 5 - A.permanent)) := by
    have h := energy_of_deficit hd0 hd1
    change energy t = _ at h
    convert h using 1; ring
  change sweepEnergy (fun i j => fiveRawConductance A (e i) (e j)) f ≤ energy t * U
  rw [hE, henergy]
  have heq : 10 * dittertSpectralGap A * (height t / 10 * U) =
      height t * dittertSpectralGap A * U := by ring
  rw [heq] at hraw
  rw [← mul_div_assoc] at hupper
  exact hraw.trans hupper


/-- Every odd-cardinality prefix is unbalanced and hence has boundary at least `q`. -/
theorem five_odd_prefix_boundary (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2 - dittertConstant 5 ≤ dittertFunctional A)
    (e : Fin 10 ≃ SquareVertices 5) (r : Fin 9) (hodd : Odd (r.val + 1)) :
    domination (fiveDeficitParameter (dittertConstant 5 - A.permanent)) ≤
      sweepBoundary (fun i j => fiveRawConductance A (e i) (e j)) (sweepPrefix r) := by
  let S := (sweepPrefix r).map e.toEmbedding
  have hcard : S.toLeft.card + S.toRight.card = r.val + 1 := by
    rw [Finset.card_toLeft_add_card_toRight]
    simp [S, sweepPrefix_card]
  have hneq : S.toLeft.card ≠ S.toRight.card := by
    intro heq
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := five_contender_unbalanced_crossing A hA hmass hcont S.toLeft S.toRight hneq
  rw [sweepBoundary_equiv, fiveRawBoundary]
  exact h

/-- A small-boundary sorted score prefix yields one of the two precisely
oriented balanced cuts used by the actual order-five permanent contradiction. -/
theorem five_oriented_cut_of_score_prefix (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A)
    (S : Finset (SquareVertices 5)) (hS : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hbound : sweepBoundary (fiveRawConductance A) S ≤
      crossingBound (fiveDeficitParameter (dittertConstant 5 - A.permanent)))
    (hlower : ∀ v ∈ S, ∀ w ∈ Sᶜ, dittertSpectralScore A v ≤ dittertSpectralScore A w) :
    ∃ I J : Finset (Fin 5), I.card = J.card ∧ 1 ≤ I.card ∧ I.card ≤ 2 ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        crossingBound (fiveDeficitParameter (dittertConstant 5 - A.permanent)) ∧
      (LowerMarginalCut A I J ∨ LowerMarginalCut A.transpose J I) ∧
      (((∑ i ∈ I, rowSum A i) ≤ I.card ∧ (J.card : ℝ) ≤ ∑ j ∈ J, colSum A j) ∨
        ((I.card : ℝ) ≤ (∑ i ∈ I, rowSum A i) ∧ (∑ j ∈ J, colSum A j) ≤ J.card)) ∧
      (I.card = 1 → ∀ i ∈ I, ∀ j ∈ J,
        ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
        ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  let t := fiveDeficitParameter (dittertConstant 5 - A.permanent)
  have ht : 0 ≤ t := fiveDeficitParameter_nonneg _
  have htcap : t ≤ 9 / 20 := (fiveDeficitParameter_lt_cap hd0 hdg).le
  have hwq : crossingBound t < domination t := by
    have hw := crossingBound_lt_thirteen_fiftieths t ht htcap
    have hq := domination_ge_eleven_twentieths htcap
    linarith
  have hcard : S.toLeft.card = S.toRight.card := by
    by_contra hne
    have hh := five_contender_unbalanced_crossing A hA hmass hcont S.toLeft S.toRight hne
    rw [fiveRawBoundary] at hbound
    exact (not_lt_of_ge (hh.trans hbound)) hwq
  have hsum : S.toLeft.card + S.toRight.card = S.card := Finset.card_toLeft_add_card_toRight
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hlt : S.card < 10 := by
    simpa [SquareVertices] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
  have hLo : 1 ≤ S.toLeft.card := by omega
  have hHi : S.toLeft.card < 5 := by omega
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨ha, hb⟩ := dittert_contender_stationary_coefficients_pos (by norm_num) A hA hmass hcont
  by_cases hsmall : S.toLeft.card ≤ 2
  · refine ⟨S.toLeft, S.toRight, hcard, hLo, hsmall, ?_, ?_, ?_, ?_⟩
    · rwa [fiveRawBoundary] at hbound
    · exact Or.inl (lower_score_cut_order A _ _ ha hb hr hc S hlower)
    · exact Or.inl (lower_score_cut_marginal_sums (by norm_num) A _ _ ha hb hr hc hmass S hlower)
    · intro hone i hi j hj
      obtain ⟨a, haS⟩ := Finset.card_eq_one.mp hone
      have hai : i = a := by simpa [haS] using hi
      have hLi : S.toLeft = {i} := by simpa [← hai] using haS
      obtain ⟨b, hbS⟩ := Finset.card_eq_one.mp (hcard ▸ hone)
      have hbj : j = b := by simpa [hbS] using hj
      have hRj : S.toRight = {j} := by simpa [← hbj] using hbS
      exact Or.inl (singleton_lower_score_cut_extrema A _ _ ha hb hr hc S i j hLi hRj hlower)
  · have hLc : (Sᶜ).toLeft = S.toLeftᶜ := by ext i; simp
    have hRc : (Sᶜ).toRight = S.toRightᶜ := by ext j; simp
    have hLcard : (Sᶜ).toLeft.card = 5 - S.toLeft.card := by rw [hLc, Finset.card_compl]; simp
    have hRcard : (Sᶜ).toRight.card = 5 - S.toRight.card := by rw [hRc, Finset.card_compl]; simp
    have hcard' : (Sᶜ).toLeft.card = (Sᶜ).toRight.card := by omega
    have hLo' : 1 ≤ (Sᶜ).toLeft.card := by omega
    have hHi' : (Sᶜ).toLeft.card ≤ 2 := by omega
    refine ⟨(Sᶜ).toLeft, (Sᶜ).toRight, hcard', hLo', hHi', ?_, ?_, ?_, ?_⟩
    · rw [← fiveRawBoundary, sweepBoundary_compl _ (fiveRawConductance_symm A)]
      exact hbound
    · apply Or.inr
      apply upper_score_cut_order A _ _ ha hb hr hc (Sᶜ)
      intro v hv w hw
      exact hlower w (by simpa using hw) v hv
    · apply Or.inr
      apply upper_score_cut_marginal_sums (by norm_num) A _ _ ha hb hr hc hmass (Sᶜ)
      intro v hv w hw
      exact hlower w (by simpa using hw) v hv
    · intro hone i hi j hj
      obtain ⟨a, haS⟩ := Finset.card_eq_one.mp hone
      have hai : i = a := by simpa [haS] using hi
      have hLi : (Sᶜ).toLeft = {i} := by simpa [← hai] using haS
      obtain ⟨b, hbS⟩ := Finset.card_eq_one.mp (hcard' ▸ hone)
      have hbj : j = b := by simpa [hbS] using hj
      have hRj : (Sᶜ).toRight = {j} := by simpa [← hbj] using hbS
      apply Or.inr
      apply singleton_upper_score_cut_extrema A _ _ ha hb hr hc (Sᶜ) i j hLi hRj
      intro v hv w hw
      exact hlower w (by simpa using hw) v hv

end DittertRybin
