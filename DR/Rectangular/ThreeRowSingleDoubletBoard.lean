import DR.Rectangular.ThreeRowFullOffsets

/-! The actual two-class matrix and all four first-order conditions for a single doubleton type. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def threeRowSingleDoubletBoard {n : ℕ} (i : Fin 3) (s : Finset (Fin n))
    (b c d : ℝ) : Board 3 n := fun r j =>
  if r = i then (if j ∈ s then 0 else c) else (if j ∈ s then b else d)

private theorem sum_two_classes {n : ℕ} (s : Finset (Fin n)) (x y : ℝ) :
    (∑ j, if j ∈ s then x else y) = (s.card : ℝ) * x + (sᶜ.card : ℝ) * y := by
  classical
  rw [Finset.sum_ite]
  have he : Finset.univ.filter (fun j => j ∉ s) = sᶜ := by ext j; simp
  simp [he]

theorem rowSum_threeRowSingleDoubletBoard {n : ℕ} (i : Fin 3) (s : Finset (Fin n))
    (b c d : ℝ) (r : Fin 3) :
    rowSum (threeRowSingleDoubletBoard i s b c d) r =
      if r = i then (sᶜ.card : ℝ) * c else (s.card : ℝ) * b + (sᶜ.card : ℝ) * d := by
  classical
  unfold rowSum threeRowSingleDoubletBoard
  split_ifs with hr
  · rw [sum_two_classes]
    ring
  · exact sum_two_classes s b d

/-- No sign or mass hypothesis enters the two row-pair moment identities. -/
theorem threeRowPair_threeRowSingleDoubletBoard {n : ℕ} (i h k : Fin 3)
    (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k) (s : Finset (Fin n)) (b c d : ℝ) :
    threeRowPair (threeRowSingleDoubletBoard i s b c d) i = (s.card : ℝ) * b ^ 2 + (sᶜ.card : ℝ) * d ^ 2 ∧
    threeRowPair (threeRowSingleDoubletBoard i s b c d) h = (sᶜ.card : ℝ) * c * d := by
  classical
  rw [threeRowPair_eq_other_rows _ i h k hih hik hhk,
    threeRowPair_eq_other_rows _ h i k hih.symm hhk hik]
  simp only [threeRowSingleDoubletBoard, hih.symm, hik.symm, if_false, if_true]
  constructor
  · have he (j : Fin n) : (if j ∈ s then b else d) * (if j ∈ s then b else d) =
        if j ∈ s then b ^ 2 else d ^ 2 := by split_ifs <;> ring
    simp only [he]
    exact sum_two_classes s _ _
  · have he (j : Fin n) : (if j ∈ s then 0 else c) * (if j ∈ s then b else d) =
        if j ∈ s then 0 else c * d := by split_ifs <;> ring
    simp only [he]
    rw [sum_two_classes]
    ring

/-- A global maximum with the displayed actual block form satisfies the column equations
and both the positive-row equality and the zero-row inequality. -/
theorem IsSeparationGlobalMax.threeRow_single_doublet_board_kkt {n : ℕ}
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (s : Finset (Fin n)) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (a q : Fin n) (ha : a ∈ s) (hq : q ∉ s)
    (hP : IsProbability (threeRowSingleDoubletBoard i s b c d))
    (hmax : IsSeparationGlobalMax (threeRowSingleDoubletBoard i s b c d) 3) :
    let S : ℝ := s.card
    let T : ℝ := sᶜ.card
    let X := (T - 1) * c
    let Y := (S - 1) * b + (T - 1) * d
    (b-d)*(X+4*Y) = c*(X+Y) ∧
    0 ≤ -(X+2*Y)*c+2*(X+Y)*(b-d) ∧
    (c-d)*(S*b+(3*T-2)*d) = S*b*(b+d) ∧
    b*((3*S-2)*b+T*d)-T*(c-d)*(b+d) ≤ 0 := by
  classical
  let P := threeRowSingleDoubletBoard i s b c d
  change IsProbability P at hP
  change IsSeparationGlobalMax P 3 at hmax
  have hia : P i a = 0 := by simp [P, threeRowSingleDoubletBoard, ha]
  have hha : P h a = b := by simp [P, threeRowSingleDoubletBoard, ha, hih.symm]
  have hka : P k a = b := by simp [P, threeRowSingleDoubletBoard, ha, hik.symm]
  have hiq : P i q = c := by simp [P, threeRowSingleDoubletBoard, hq]
  have hhq : P h q = d := by simp [P, threeRowSingleDoubletBoard, hq, hih.symm]
  have hkq : P k q = d := by simp [P, threeRowSingleDoubletBoard, hq, hik.symm]
  have hri : rowSum P i = (sᶜ.card : ℝ) * c := by simp [P, rowSum_threeRowSingleDoubletBoard]
  have hrh : rowSum P h = (s.card : ℝ) * b + (sᶜ.card : ℝ) * d := by
    simp [P, rowSum_threeRowSingleDoubletBoard, hih.symm]
  have hrk : rowSum P k = (s.card : ℝ) * b + (sᶜ.card : ℝ) * d := by
    simp [P, rowSum_threeRowSingleDoubletBoard, hik.symm]
  have hmass := threeRowRemainingRow_sum_other_rows P a q i h k hih hik hhk
  have hcol := hmax.threeRow_comparison_eq_zero hP a q h (by rwa [hha]) (by rwa [hhq])
  have hzero := hmax.threeRow_comparison_nonneg hP a q i (by rwa [hiq])
  rw [threeRowColumnComparison_dot P a q h i k hih.symm hhk hik, ← hmass] at hcol
  rw [threeRowColumnComparison_dot P a q i h k hih hik hhk, ← hmass] at hzero
  simp only [threeRowRemainingRow, hri, hrh, hrk, hia, hha, hka, hiq, hhq, hkq] at hcol hzero
  obtain ⟨hpi, hph⟩ := threeRowPair_threeRowSingleDoubletBoard i h k hih hik hhk s b c d
  change threeRowPair P i = _ at hpi
  change threeRowPair P h = _ at hph
  have hrow := hmax.threeRow_gradient_eq hP (i,q) (h,q) (by rwa [hiq]) (by rwa [hhq])
  have hrowzero := hmax.threeRow_gradient_le hP (i,a) (h,a) (by rwa [hha])
  dsimp at hrow hrowzero
  rw [threeRowReducedGradient_reindex P i h k hih hik hhk,
    threeRowReducedGradient_reindex P h i k hih.symm hhk hik] at hrow hrowzero
  simp only [hpi, hph, hri, hrh, hrk, hia, hha, hka, hiq, hhq, hkq] at hrow hrowzero
  dsimp
  constructor
  · nlinarith only [hcol]
  constructor
  · nlinarith only [hzero]
  constructor
  · nlinarith only [hrow]
  · nlinarith only [hrowzero]

end DittertRybin
