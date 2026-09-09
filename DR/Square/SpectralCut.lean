import DR.Square.SpectralPair
import DR.Square.SweepReindex
import DR.Square.MarginalDiscrepancy
import DR.Square.BlockFloor

/-!
# Actual matrix cuts obtained from the stationary spectral score

The finite weighted sweep is converted back to row and column subsets.
All cut volumes and crossing masses refer to the original matrix.
-/

namespace DittertRybin

open scoped BigOperators

theorem squareSweepMass {n : ℕ} (A : Board n n) (S : Finset (SquareVertices n)) :
    sweepMass (squareVertexWeight A) S =
      ((∑ i ∈ S.toLeft, rowSum A i) + (∑ j ∈ S.toRight, colSum A j)) / (2 * n) := by
  unfold sweepMass
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp only [squareVertexWeight, ← Finset.sum_div, add_div]

theorem squareSweepBoundary {n : ℕ} (A : Board n n) (S : Finset (SquareVertices n)) :
    sweepBoundary (squareConductance A) S =
      (cutMass A S.toLeft S.toRightᶜ + cutMass A S.toLeftᶜ S.toRight) / (2 * n) := by
  have hl : Sᶜ.toLeft = S.toLeftᶜ := by ext i; simp
  have hr : Sᶜ.toRight = S.toRightᶜ := by ext j; simp
  unfold sweepBoundary
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp_rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp only [squareConductance, Finset.sum_const_zero, zero_add, add_zero, hl, hr,
    ← Finset.sum_div]
  rw [Finset.sum_comm (s := S.toRight)]
  exact (add_div _ _ _).symm

/-- A nonuniform global maximizer produces a proper matrix cut of at most half the volume. -/
theorem dittert_globalMax_cut {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix n) :
    ∃ I J : Finset (Fin n), 0 < I.card + J.card ∧ I.card + J.card < 2 * n ∧
      (∑ i ∈ I, rowSum A i) + (∑ j ∈ J, colSum A j) ≤ n ∧
      cutMass A I Jᶜ + cutMass A Iᶜ J ≤
        (n : ℝ) * (2 * n - 1) * A.permanent / (2 * (1 - (dittertConstant n - A.permanent))) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  have hV := dittert_globalMax_variance_pos hn A hA hmass hmax hu
  obtain ⟨S, hS, hproper, hmassS, hcross⟩ := exists_weighted_sweep_cut_fintype
    (α := SquareVertices n) (by simp [SquareVertices]; omega)
    (squareVertexWeight A) (squareVertexWeight_pos (by omega) A hr hc)
    (squareVertexWeight_sum (by omega) A hmass) (squareConductance A)
    (squareConductance_nonneg A hA) (squareConductance_symm A) (dittertSpectralScore A) hV
  have hcard : S.toLeft.card + S.toRight.card = S.card := S.card_toLeft_add_card_toRight
  refine ⟨S.toLeft, S.toRight, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hS.card_pos
  · rw [hcard]
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa [SquareVertices, two_mul] using h
  · rw [squareSweepMass] at hmassS
    have h := (div_le_iff₀ (show (0 : ℝ) < 2 * n by positivity)).mp hmassS
    linarith
  · rw [squareSweepBoundary, dittert_globalMax_energy hn A hA hmass hmax] at hcross
    have hfactor : ((Fintype.card (SquareVertices n) - 1 : ℕ) : ℝ) = 2 * n - 1 := by
      simp [SquareVertices, Nat.cast_sub (show 1 ≤ n + n by omega)]
      ring
    rw [hfactor] at hcross
    have hcancel : (2 * (n : ℝ) - 1) *
        (dittertSpectralGap A * sweepVariance (squareVertexWeight A) (dittertSpectralScore A)) /
        (4 * sweepVariance (squareVertexWeight A) (dittertSpectralScore A)) =
        (2 * n - 1) * dittertSpectralGap A / 4 := by field_simp
    rw [hcancel] at hcross
    have hgap := (dittert_globalMax_gap_bounds hn A hA hmass hmax hu).2
    have hstep := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * (n : ℝ) - 1 by
      have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn; linarith)
    have hraw := (div_le_iff₀ (show (0 : ℝ) < 2 * n by positivity)).mp hcross
    have hm := mul_le_mul_of_nonneg_left hstep hn0.le
    calc
      _ ≤ (2 * (n : ℝ) - 1) * dittertSpectralGap A / 4 * (2 * n) := hraw
      _ ≤ (n * ((2 * n - 1) *
          (A.permanent / (1 - (dittertConstant n - A.permanent))))) / 2 := by nlinarith
      _ = _ := by simp only [div_mul_eq_div_div]; ring

/-- The elementary capacity lower bound from the two marginal sums. -/
theorem cutMass_ge_marginal_sum_sub_mass {n : ℕ} (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (I J : Finset (Fin n)) :
    (∑ i ∈ I, rowSum A i) + (∑ j ∈ J, colSum A j) - totalMass A ≤ cutMass A I J := by
  have h1 := cutMass_add_compl_cols A I J
  have h2 := cutMass_add_compl_rows A I Jᶜ
  have h3 := Finset.sum_add_sum_compl J (colSum A)
  rw [← totalMass_eq_sum_colSum] at h3
  have h0 := cutMass_nonneg hA Iᶜ Jᶜ
  linarith

/-- Uniform subset discrepancy supplies every transport cut, including nonpositive demand. -/
theorem transportCuts_of_shared_discrepancy {n : ℕ} (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n) (d : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1)
    (hdisc : ∀ I J : Finset (Fin n),
      |(∑ i ∈ I, rowSum A i) - I.card| + |(∑ j ∈ J, colSum A j) - J.card| ≤ d) :
    TransportCuts A (1 - d) := by
  intro I J
  by_cases h : I.card + J.card ≤ n
  · have hcast : (I.card : ℝ) + J.card - n ≤ 0 := by
      have : (I.card : ℝ) + J.card ≤ n := by exact_mod_cast h
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hcast).trans (cutMass_nonneg hA I J)
  · have hcast : (1 : ℝ) ≤ I.card + J.card - n := by
      have : n + 1 ≤ I.card + J.card := by omega
      have := Nat.cast_le (α := ℝ).mpr this
      push_cast at this
      linarith
    have hlow := cutMass_ge_marginal_sum_sub_mass A hA I J
    rw [hmass] at hlow
    have hdij := hdisc I J
    have hi := neg_abs_le ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
    have hj := neg_abs_le ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
    nlinarith

/-- A cut of total discrepancy plus crossing mass below one has equal axis cardinalities. -/
theorem cut_card_eq_of_shared_discrepancy {n : ℕ} (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (I J : Finset (Fin n)) (d w : ℝ)
    (hdisc : |(∑ i ∈ I, rowSum A i) - I.card| + |(∑ j ∈ J, colSum A j) - J.card| ≤ d)
    (hcross : cutMass A I Jᶜ + cutMass A Iᶜ J ≤ w) (hsmall : w + d < 1) :
    I.card = J.card := by
  have hrows := cutMass_add_compl_cols A I J
  have hcols := cutMass_add_compl_rows A I J
  have hleft := cutMass_nonneg hA I Jᶜ
  have hright := cutMass_nonneg hA Iᶜ J
  have hi₁ := le_abs_self ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hi₂ := neg_abs_le ((∑ i ∈ I, rowSum A i) - (I.card : ℝ))
  have hj₁ := le_abs_self ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  have hj₂ := neg_abs_le ((∑ j ∈ J, colSum A j) - (J.card : ℝ))
  rcases lt_trichotomy I.card J.card with h | h | h
  · have hcast : (I.card : ℝ) + 1 ≤ J.card := by exact_mod_cast h
    linarith
  · exact h
  · have hcast : (J.card : ℝ) + 1 ≤ I.card := by exact_mod_cast h
    linarith

end DittertRybin
