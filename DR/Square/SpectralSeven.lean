import DR.Square.SpectralAssembly
import DR.Square.RefinedSweep

/-! The refined fourteen-vertex path closes the actual square argument at order seven. -/

namespace DittertRybin

open scoped BigOperators
open Certificates.SpectralParameters

/-- The sharper cut comes from the actual stationary score and actual marginal cap. -/
theorem dittert_globalMax_cut_seven (A : Board 7 7)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 7)
    (hmax : ∀ B : Board 7 7, (∀ i j, 0 ≤ B i j) → totalMass B = 7 →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix 7) :
    ∃ I J : Finset (Fin 7), 0 < I.card + J.card ∧ I.card + J.card < 14 ∧
      (∑ i ∈ I, rowSum A i) + (∑ j ∈ J, colSum A j) ≤ 7 ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        23 * A.permanent / (1 - (dittertConstant 7 - A.permanent)) := by
  have hcont := dittert_globalMax_isContender (by decide : 0 < 7) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by decide : 2 ≤ 7) A hA hmass hcont
  obtain ⟨hrcap, hccap⟩ := dittert_contender_marginal_cap_seven A hA hmass hcont
  have hV := dittert_globalMax_variance_pos (by decide : 2 ≤ 7) A hA hmass hmax hu
  let e : Fin 14 ≃ SquareVertices 7 := (Fintype.equivFin (SquareVertices 7)).symm
  have hπpos (i : Fin 14) : 0 < (squareVertexWeight A ∘ e) i :=
    squareVertexWeight_pos (by decide) A hr hc (e i)
  have hπsum : ∑ v, (squareVertexWeight A ∘ e) v = 1 :=
    (Equiv.sum_comp e _).trans (squareVertexWeight_sum (by decide) A hmass)
  have hV' : 0 < sweepVariance (squareVertexWeight A ∘ e) (dittertSpectralScore A ∘ e) := by
    rwa [sweepVariance_equiv]
  have hcap (i : Fin 14) : (squareVertexWeight A ∘ e) i ≤ 23 / 280 := by
    dsimp only [Function.comp_def]
    cases e i with
    | inl r => dsimp [squareVertexWeight]; linarith [hrcap r]
    | inr c => dsimp [squareVertexWeight]; linarith [hccap c]
  obtain ⟨T, hT, hproper, hmassT, hcrossT⟩ := exists_refined_weighted_sweep_cut
    (squareVertexWeight A ∘ e) hπpos hπsum (23 / 280) hcap
    (fun i j => squareConductance A (e i) (e j))
    (fun i j => squareConductance_nonneg A hA (e i) (e j))
    (fun i j => squareConductance_symm A (e i) (e j)) (dittertSpectralScore A ∘ e) hV'
  let S := T.map e.toEmbedding
  have hS : S.Nonempty := Finset.map_nonempty.mpr hT
  have hproperS : S ≠ Finset.univ := by
    intro h
    apply hproper
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : e i ∈ S := h ▸ Finset.mem_univ _
    simpa [S] using hi
  have hmassS : sweepMass (squareVertexWeight A) S ≤ 1 / 2 := by
    rwa [sweepMass_equiv]
  have hcross : sweepBoundary (squareConductance A) S ≤
      20 * (23 / 280) * sweepEnergy (squareConductance A) (dittertSpectralScore A) /
        sweepVariance (squareVertexWeight A) (dittertSpectralScore A) := by
    simpa only [sweepBoundary_equiv, sweepEnergy_equiv, sweepVariance_equiv] using hcrossT
  have hcard : S.toLeft.card + S.toRight.card = S.card := S.card_toLeft_add_card_toRight
  refine ⟨S.toLeft, S.toRight, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hS.card_pos
  · rw [hcard]
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproperS)
    simpa [SquareVertices] using h
  · rw [squareSweepMass] at hmassS
    norm_num at hmassS
    linarith
  · rw [squareSweepBoundary, dittert_globalMax_energy (by decide : 2 ≤ 7) A hA hmass hmax] at hcross
    have hcancel : 20 * (23 / 280 : ℝ) *
        (dittertSpectralGap A * sweepVariance (squareVertexWeight A) (dittertSpectralScore A)) /
        sweepVariance (squareVertexWeight A) (dittertSpectralScore A) =
        (23 / 14) * dittertSpectralGap A := by field_simp; ring
    rw [hcancel] at hcross
    have hgap := (dittert_globalMax_gap_bounds (by decide : 2 ≤ 7) A hA hmass hmax hu).2
    norm_num only [Nat.cast_ofNat] at hcross
    calc
      _ ≤ 23 * dittertSpectralGap A := by linarith
      _ ≤ 23 * (A.permanent / (1 - (dittertConstant 7 - A.permanent))) := by linarith
      _ = _ := by ring

/-- Every global maximizer at order seven is uniform, with no support assumption. -/
theorem dittert_globalMax_uniform_seven (A : Board 7 7)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 7)
    (hmax : ∀ B : Board 7 7, (∀ i j, 0 ≤ B i j) → totalMass B = 7 →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix 7 := by
  by_contra hu
  have hcont := dittert_globalMax_isContender (by decide : 0 < 7) A hmax
  obtain ⟨z, hz, hz1, hdelta⟩ := dittert_contender_deficit_coordinate (by decide : 2 ≤ 7) A hA hmass hcont
  obtain ⟨I, J, hnonempty, hproper, _, hcross⟩ := dittert_globalMax_cut_seven A hA hmass hmax hu
  have ha : 0 ≤ rootParameter 7 := Real.sqrt_nonneg _
  have hb : 0 ≤ sweepParameterSeven := by norm_num [sweepParameterSeven, dittertConstant, Nat.factorial]
  have hsmall : rootParameter 7 + 2 * sweepParameterSeven < 1 := by
    linarith [rootParameter_seven_le, sweepParameter_seven_le]
  apply spectral_cut_contradiction (by decide : 2 ≤ 7) A hA hmass (rootParameter 7) sweepParameterSeven z
    ha hb hz hz1 hsmall (by linarith)
    (dittert_contender_discrepancy_coordinate (by decide : 2 ≤ 7) A hA hmass hcont z hz hdelta)
    I J hnonempty hproper _ (by convert spectral_gap_seven z hz hz1 using 1; norm_num)
  have hbound := spectral_crossing_coordinate (by decide : 2 ≤ 7) A hA hmass hcont z 23 (by norm_num) hdelta
  have heq : (23 * dittertConstant 7 / (1 - dittertConstant 7)) * (1 - z ^ 2) =
      2 * sweepParameterSeven * (1 - z ^ 2) := by
    simp only [sweepParameterSeven, div_mul_eq_div_div]; ring
  rw [heq] at hbound
  exact hcross.trans hbound

theorem dittert_order_seven : DittertMaximizer 7 :=
  dittertMaximizer_of_globalMax_uniform (by decide) dittert_globalMax_uniform_seven

/-- The complete spectral range, with sharp inequality and iff equality. -/
theorem dittert_ge_seven {n : ℕ} (hn : 7 ≤ n) : DittertMaximizer n := by
  obtain h | h := eq_or_lt_of_le hn
  · subst n; exact dittert_order_seven
  · exact dittert_ge_eight (by omega)

end DittertRybin
