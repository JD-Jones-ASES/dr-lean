import DR.Endpoint.CutDeficit

/-! The minimum-dilation choice for rectangular real capacities.
Every positive cut is assumed to have positive actual mass. The finite
minimum constructs a balanced board and forces the complementary zero
rectangle at an active cut. No minimum permanent is assumed. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def rectangularCutDemand {m n : ℕ}
    (I : Finset (Fin m)) (J : Finset (Fin n)) : ℝ :=
  (I.card : ℝ)/m + (J.card : ℝ)/n - 1

theorem rectangularCutDemand_univ {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    rectangularCutDemand (Finset.univ : Finset (Fin m)) (Finset.univ : Finset (Fin n)) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [rectangularCutDemand, hm0, hn0]

theorem balanced_cut_complement_identity {m n : ℕ} {B : Board m n}
    (hB : IsProbability B) (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass B I J = rectangularCutDemand I J + cutMass B Iᶜ Jᶜ := by
  rw [cutMass_eq_marginal_deficit_add_complement, hB.2]
  simp only [hr, hc, Finset.sum_const, nsmul_eq_mul, rectangularCutDemand]
  ring

/-- An active cut forces a zero complementary rectangle in the actual
balanced board, including all axis and whole-matrix cuts. -/
theorem active_dilation_cut_complement_zero {m n : ℕ} {P B : Board m n} {q : ℝ}
    (hq : 0 < q) (hB : IsProbability B)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ)) (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (hdom : ∀ i j, q*B i j ≤ P i j)
    (I : Finset (Fin m)) (J : Finset (Fin n))
    (hactive : cutMass P I J = q*rectangularCutDemand I J) :
    cutMass B Iᶜ Jᶜ = 0 := by
  have hcut := cutMass_mono (A := q • B) (B := P) hdom I J
  rw [cutMass_smul, hactive] at hcut
  have hle := (mul_le_mul_iff_right₀ hq).mp hcut
  have hid := balanced_cut_complement_identity hB hr hc I J
  exact le_antisymm (by linarith) (cutMass_nonneg hB.1 _ _)

/-- A true minimum over all positive cuts supplies balanced domination and
an active zero rectangle. Individual original cells may vanish. -/
theorem exists_minimum_rectangular_dilation {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P : Board m n} (hP : IsProbability P)
    (hpositive : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      0 < rectangularCutDemand I J → 0 < cutMass P I J) :
    ∃ (q : ℝ) (B : Board m n) (I : Finset (Fin m)) (J : Finset (Fin n)),
      0 < q ∧ q ≤ 1 ∧ IsProbability B ∧
      (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      (∀ i j, q*B i j ≤ P i j) ∧ 0 < rectangularCutDemand I J ∧
      cutMass P I J = q*rectangularCutDemand I J ∧ cutMass B Iᶜ Jᶜ = 0 := by
  classical
  let S : Finset (Finset (Fin m) × Finset (Fin n)) :=
    Finset.univ.filter fun IJ => 0 < rectangularCutDemand IJ.1 IJ.2
  have hu : (Finset.univ, Finset.univ) ∈ S := by
    simp [S, rectangularCutDemand_univ hm hn]
  let f : Finset (Fin m) × Finset (Fin n) → ℝ :=
    fun IJ => cutMass P IJ.1 IJ.2 / rectangularCutDemand IJ.1 IJ.2
  obtain ⟨IJ, hIJ, hmin⟩ := S.exists_min_image f ⟨_, hu⟩
  have hp : 0 < rectangularCutDemand IJ.1 IJ.2 := (Finset.mem_filter.mp hIJ).2
  let q := f IJ
  have hq : 0 < q := div_pos (hpositive _ _ hp) hp
  have hfU : f (Finset.univ, Finset.univ) = 1 := by
    dsimp [f]
    rw [rectangularCutDemand_univ hm hn]
    change totalMass P / 1 = 1
    rw [hP.2, div_one]
  have hq1 : q ≤ 1 := by simpa only [hfU] using hmin _ hu
  have hcuts : RectangularTransportCuts ((1/q) • P) := by
    intro I J
    rw [cutMass_smul, one_div_mul_eq_div]
    change rectangularCutDemand I J ≤ cutMass P I J/q
    by_cases hp' : 0 < rectangularCutDemand I J
    · have hmem : (I,J) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'⟩
      have hbound : q ≤ cutMass P I J/rectangularCutDemand I J := hmin _ hmem
      have hprod := (le_div_iff₀ hp').mp hbound
      apply (le_div_iff₀ hq).mpr
      nlinarith only [hprod]
    · exact (le_of_not_gt hp').trans (div_nonneg (cutMass_nonneg hP.1 _ _) hq.le)
  have hscaled : ∀ i j, 0 ≤ ((1/q) • P) i j :=
    fun i j => mul_nonneg (one_div_nonneg.mpr hq.le) (hP.1 i j)
  obtain ⟨B, hB⟩ := exists_rectangularTransport_of_cuts hm hn _ hscaled hcuts
  have hBP : ∀ i j, q*B i j ≤ P i j := by
    intro i j
    have h := hB.2.1 i j
    change B i j ≤ (1/q)*P i j at h
    rw [one_div_mul_eq_div] at h
    have h' := (le_div_iff₀ hq).mp h
    nlinarith only [h']
  have hactive : cutMass P IJ.1 IJ.2 = q*rectangularCutDemand IJ.1 IJ.2 := by
    dsimp [q, f]
    field_simp
  have hBprob := hB.isProbability hm
  exact ⟨q, B, IJ.1, IJ.2, hq, hq1, hBprob, hB.2.2.1, hB.2.2.2, hBP, hp,
    hactive, active_dilation_cut_complement_zero hq hBprob hB.2.2.1 hB.2.2.2 hBP _ _ hactive⟩

/-- Any competing nonnegative dilation is bounded by the active cut ratio. -/
theorem rectangular_dilation_le_active {m n : ℕ} {P C : Board m n} {q u : ℝ}
    (hu : 0 ≤ u) (hC : IsProbability C)
    (hr : ∀ i, rowSum C i = 1/(m : ℝ)) (hc : ∀ j, colSum C j = 1/(n : ℝ))
    (hdom : ∀ i j, u*C i j ≤ P i j)
    (I : Finset (Fin m)) (J : Finset (Fin n))
    (hp : 0 < rectangularCutDemand I J)
    (hactive : cutMass P I J = q*rectangularCutDemand I J) : u ≤ q := by
  have hcut := cutMass_mono (A := u • C) (B := P) hdom I J
  rw [cutMass_smul, hactive] at hcut
  have hid := balanced_cut_complement_identity hC hr hc I J
  have hcomp := cutMass_nonneg hC.1 Iᶜ Jᶜ
  have hlow : rectangularCutDemand I J ≤ cutMass C I J := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlow hu
  exact (mul_le_mul_iff_left₀ hp).mp (hmul.trans hcut)

/-- Unit dilation and equal total mass identify the original and balanced boards. -/
theorem probability_eq_of_entrywise_le {m n : ℕ} {P B : Board m n}
    (hP : IsProbability P) (hB : IsProbability B) (hdom : ∀ i j, B i j ≤ P i j) :
    P = B := by
  have hsum : (∑ i, ∑ j, (P i j-B i j)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    change totalMass P-totalMass B = 0
    rw [hP.2, hB.2, sub_self]
  have hrows := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hdom i j)))).mp hsum
  ext i j
  have hi := hrows i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sub_nonneg.mpr (hdom i j))).mp hi j (Finset.mem_univ j)
  exact sub_eq_zero.mp hj

end DittertRybin
