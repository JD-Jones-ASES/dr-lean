import DR.Square.SixMatrixBounds
import DR.Square.ScoreOrder
import DR.Square.RefinedSweep
import Mathlib.Order.Interval.Finset.Fin

/-!
# Actual sorted score and raw conductance at order six

These identities prepare the alternating sweep on the actual twelve matrix
vertices. Conductance is unnormalized here, so its cut boundary is exactly
the sum of the two off-diagonal matrix rectangles.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralSixGuards

noncomputable def sixSortedVertices (A : Board 6 6) : Fin 12 ≃ SquareVertices 6 :=
  let e : Fin 12 ≃ SquareVertices 6 := (Fintype.equivFin (SquareVertices 6)).symm
  (Tuple.sort (dittertSpectralScore A ∘ e)).trans e

noncomputable def sixRawConductance (A : Board 6 6) (v w : SquareVertices 6) : ℝ :=
  12 * squareConductance A v w

theorem sixSortedScore_monotone (A : Board 6 6) :
    Monotone (dittertSpectralScore A ∘ sixSortedVertices A) := by
  exact Tuple.monotone_sort
    (dittertSpectralScore A ∘ (Fintype.equivFin (SquareVertices 6)).symm)

theorem sixRawConductance_nonneg (A : Board 6 6) (hA : ∀ i j, 0 ≤ A i j)
    (v w : SquareVertices 6) : 0 ≤ sixRawConductance A v w :=
  mul_nonneg (by norm_num) (squareConductance_nonneg A hA v w)

theorem sixRawConductance_symm (A : Board 6 6) (v w : SquareVertices 6) :
    sixRawConductance A v w = sixRawConductance A w v := by
  unfold sixRawConductance
  rw [squareConductance_symm A v w]

theorem sixRawEnergy (A : Board 6 6) (f : SquareVertices 6 → ℝ) :
    sweepEnergy (sixRawConductance A) f = 12 * sweepEnergy (squareConductance A) f := by
  simp only [sweepEnergy, sixRawConductance, mul_assoc, ← Finset.mul_sum]
  ring

theorem sixRawBoundary (A : Board 6 6) (S : Finset (SquareVertices 6)) :
    sweepBoundary (sixRawConductance A) S =
      cutMass A S.toLeft S.toRightᶜ + cutMass A S.toLeftᶜ S.toRight := by
  have heq : sweepBoundary (sixRawConductance A) S = 12 * sweepBoundary (squareConductance A) S := by
    simp only [sweepBoundary, sixRawConductance, Finset.mul_sum]
  rw [heq, squareSweepBoundary]
  norm_num
  ring

/-- A weight cap controls variance about the unweighted mean in every finite dimension. -/
theorem sweepVariance_le_cap_centered {N : ℕ} (π f : Fin N → ℝ)
    (hπ : ∑ i, π i = 1) (pmax : ℝ) (hcap : ∀ i, π i ≤ pmax) :
    sweepVariance π f ≤ pmax * ∑ i, (f i - (∑ j, f j) / N) ^ 2 := by
  calc
    _ ≤ ∑ i, π i * (f i - (∑ j, f j) / N) ^ 2 := sweepVariance_le_center π f hπ _
    _ ≤ ∑ i, pmax * (f i - (∑ j, f j) / N) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcap i) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual sorted stationary score has positive unweighted variance and
satisfies the raw energy bound needed by the alternating path. -/
theorem six_sorted_energy_bound (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix 6) :
    let e := sixSortedVertices A
    let f := dittertSpectralScore A ∘ e
    let U := ∑ i, (f i - (∑ j, f j) / 12) ^ 2
    0 < U ∧
      sweepEnergy (fun i j => sixRawConductance A (e i) (e j)) f ≤
        energy (sixDeficitParameter (dittertConstant 6 - A.permanent)) * U := by
  dsimp only
  let e := sixSortedVertices A
  let f := dittertSpectralScore A ∘ e
  let π := squareVertexWeight A ∘ e
  let t := sixDeficitParameter (dittertConstant 6 - A.permanent)
  let U := ∑ i, (f i - (∑ j, f j) / 12) ^ 2
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have ht : 0 ≤ t := sixDeficitParameter_nonneg _
  have hH : 0 < height t := by unfold height; linarith
  obtain ⟨hrcap, hccap⟩ := six_contender_marginal_cap A hA hmass hcont
  have hπsum : ∑ i, π i = 1 := (Equiv.sum_comp e _).trans (squareVertexWeight_sum (by norm_num) A hmass)
  have hπcap (i : Fin 12) : π i ≤ height t / 12 := by
    dsimp [π, Function.comp_def]
    cases e i with
    | inl r => dsimp [squareVertexWeight, height, t]; linarith [hrcap r]
    | inr c => dsimp [squareVertexWeight, height, t]; linarith [hccap c]
  have hVcap : sweepVariance π f ≤ height t / 12 * U :=
    sweepVariance_le_cap_centered π f hπsum _ hπcap
  have hV : 0 < sweepVariance π f := by
    dsimp only [π, f]
    rw [sweepVariance_equiv]
    exact dittert_globalMax_variance_pos (by norm_num) A hA hmass hmax hu
  have hU : 0 < U := by
    by_contra! hU
    have hnon := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ height t / 12) hU
    linarith
  refine ⟨hU, ?_⟩
  have hgap := dittert_globalMax_gap_bounds (by norm_num) A hA hmass hmax hu
  have hE : sweepEnergy (fun i j => sixRawConductance A (e i) (e j)) f =
      12 * dittertSpectralGap A * sweepVariance π f := by
    dsimp only [f, π]
    rw [sweepEnergy_equiv, sixRawEnergy, dittert_globalMax_energy (by norm_num) A hA hmass hmax,
      sweepVariance_equiv]
    ring
  have hraw := mul_le_mul_of_nonneg_left hVcap (by linarith : 0 ≤ 12 * dittertSpectralGap A)
  have hupper := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap.2 hH.le) hU.le
  have henergy : energy t = height t * A.permanent / (1 - (dittertConstant 6 - A.permanent)) := by
    have h := energy_of_deficit hd0 hd1
    change energy t = _ at h
    convert h using 1; ring
  change sweepEnergy (fun i j => sixRawConductance A (e i) (e j)) f ≤ energy t * U
  rw [hE, henergy]
  have heq : 12 * dittertSpectralGap A * (height t / 12 * U) =
      height t * dittertSpectralGap A * U := by ring
  rw [heq] at hraw
  rw [← mul_div_assoc] at hupper
  exact hraw.trans hupper


/-- Exact prefix cardinality, including all potential odd and even cut indices. -/
theorem sweepPrefix_card {n : ℕ} (r : Fin n) : (sweepPrefix r).card = r.val + 1 := by
  have heq : sweepPrefix r = Finset.Iic r.castSucc := by
    ext i
    simp [sweepPrefix]
    rfl
  rw [heq, Fin.card_Iic]
  rfl

/-- Mapping a monotone prefix retains all score order inequalities, including ties. -/
theorem mapped_sweepPrefix_order {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (e : Fin (n + 1) ≃ α) (f : α → ℝ) (hmono : Monotone (f ∘ e)) (r : Fin n) :
    ∀ v ∈ (sweepPrefix r).map e.toEmbedding,
      ∀ w ∈ ((sweepPrefix r).map e.toEmbedding)ᶜ, f v ≤ f w := by
  intro v hv w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
  have hnot : e.symm w ∉ sweepPrefix r := by
    intro hb
    have hmem : w ∈ (sweepPrefix r).map e.toEmbedding := by
      exact Finset.mem_map.mpr ⟨e.symm w, hb, e.apply_symm_apply w⟩
    exact (Finset.mem_compl.mp hw) hmem
  have hav : a.val ≤ r.val := by simpa [sweepPrefix] using ha
  have hwv : r.val < (e.symm w).val := by simpa [sweepPrefix] using hnot
  have h := hmono (show a ≤ e.symm w by change a.val ≤ (e.symm w).val; omega)
  change f (e a) ≤ f w
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

/-- Every odd-cardinality prefix is unbalanced and hence has boundary at least `q`. -/
theorem six_odd_prefix_boundary (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hcont : 2 - dittertConstant 6 ≤ dittertFunctional A)
    (e : Fin 12 ≃ SquareVertices 6) (r : Fin 11) (hodd : Odd (r.val + 1)) :
    sixDominationFactor (sixDeficitParameter (dittertConstant 6 - A.permanent)) ≤
      sweepBoundary (fun i j => sixRawConductance A (e i) (e j)) (sweepPrefix r) := by
  let S := (sweepPrefix r).map e.toEmbedding
  have hcard : S.toLeft.card + S.toRight.card = r.val + 1 := by
    rw [Finset.card_toLeft_add_card_toRight]
    simp [S, sweepPrefix_card]
  have hneq : S.toLeft.card ≠ S.toRight.card := by
    intro heq
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := six_contender_unbalanced_crossing A hA hmass hcont S.toLeft S.toRight hneq
  rw [sweepBoundary_equiv, sixRawBoundary]
  exact h

/-- A small-boundary sorted score prefix yields one of the two precisely
oriented balanced cuts used by the actual order-six permanent contradiction. -/
theorem six_oriented_cut_of_score_prefix (A : Board 6 6)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6)
    (hmax : ∀ B : Board 6 6, (∀ i j, 0 ≤ B i j) → totalMass B = 6 →
      dittertFunctional B ≤ dittertFunctional A)
    (S : Finset (SquareVertices 6)) (hS : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hbound : sweepBoundary (sixRawConductance A) S ≤
      crossingBound (sixDeficitParameter (dittertConstant 6 - A.permanent)))
    (hlower : ∀ v ∈ S, ∀ w ∈ Sᶜ, dittertSpectralScore A v ≤ dittertSpectralScore A w) :
    ∃ I J : Finset (Fin 6), I.card = J.card ∧ 1 ≤ I.card ∧ I.card ≤ 3 ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        crossingBound (sixDeficitParameter (dittertConstant 6 - A.permanent)) ∧
      (I.card = 1 → ∀ i ∈ I, ∀ j ∈ J,
        ((∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j)) ∨
        ((∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c))) := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨_, _, _, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  let t := sixDeficitParameter (dittertConstant 6 - A.permanent)
  have ht : 0 ≤ t := sixDeficitParameter_nonneg _
  have htcap : t ≤ 31 / 100 := (sixDeficitParameter_le_cap hd0 hdg).le
  have hwq : crossingBound t < sixDominationFactor t := by
    have hw := crossingBound_lt_one_sixth t ht htcap
    have hq := sixDominationFactor_gt_two_thirds ht htcap
    linarith
  have hcard : S.toLeft.card = S.toRight.card := by
    by_contra hne
    have hh := six_contender_unbalanced_crossing A hA hmass hcont S.toLeft S.toRight hne
    rw [sixRawBoundary] at hbound
    exact (not_lt_of_ge (hh.trans hbound)) hwq
  have hsum : S.toLeft.card + S.toRight.card = S.card := Finset.card_toLeft_add_card_toRight
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hlt : S.card < 12 := by
    simpa [SquareVertices] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
  have hLo : 1 ≤ S.toLeft.card := by omega
  have hHi : S.toLeft.card < 6 := by omega
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨ha, hb⟩ := dittert_contender_stationary_coefficients_pos (by norm_num) A hA hmass hcont
  by_cases hsmall : S.toLeft.card ≤ 3
  · refine ⟨S.toLeft, S.toRight, hcard, hLo, hsmall, ?_, ?_⟩
    · rwa [sixRawBoundary] at hbound
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
    have hLcard : (Sᶜ).toLeft.card = 6 - S.toLeft.card := by rw [hLc, Finset.card_compl]; simp
    have hRcard : (Sᶜ).toRight.card = 6 - S.toRight.card := by rw [hRc, Finset.card_compl]; simp
    have hcard' : (Sᶜ).toLeft.card = (Sᶜ).toRight.card := by omega
    have hLo' : 1 ≤ (Sᶜ).toLeft.card := by omega
    have hHi' : (Sᶜ).toLeft.card ≤ 3 := by omega
    refine ⟨(Sᶜ).toLeft, (Sᶜ).toRight, hcard', hLo', hHi', ?_, ?_⟩
    · rw [← sixRawBoundary, sweepBoundary_compl _ (sixRawConductance_symm A)]
      exact hbound
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
