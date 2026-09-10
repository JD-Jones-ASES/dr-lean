import DR.Endpoint.CutDeficitGrid

/-! Marginal subset discrepancies imply every balanced rectangular transport
cut after one common scaling. Positive cuts use the common-divisor grid;
nonpositive cuts follow directly from nonnegative capacities. -/
namespace DittertRybin
open scoped BigOperators

/-- The exact complementary-rectangle identity, with no sign or mass condition. -/
theorem cutMass_eq_marginal_deficit_add_complement {m n : ℕ} (P : Board m n)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass P I J = (∑ i ∈ I, rowSum P i) + (∑ j ∈ J, colSum P j) -
      totalMass P + cutMass P Iᶜ Jᶜ := by
  have hr := cutMass_add_compl_cols P I J
  have hc := cutMass_add_compl_rows P I Jᶜ
  have ht := Finset.sum_add_sum_compl J (colSum P)
  rw [← totalMass_eq_sum_colSum] at ht
  linarith

/-- A bound on the two actual marginal subset deviations bounds cut loss. -/
theorem cutMass_lower_of_subset_discrepancy {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (I : Finset (Fin m)) (J : Finset (Fin n))
    {ε : ℝ} (hdev : |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ ε) :
    (I.card : ℝ)/m + (J.card : ℝ)/n - 1 - ε ≤ cutMass P I J := by
  have hi := neg_abs_le ((∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m)
  have hj := neg_abs_le ((∑ j ∈ J, colSum P j) - (J.card : ℝ)/n)
  have hc := cutMass_nonneg hP.1 Iᶜ Jᶜ
  have hid := cutMass_eq_marginal_deficit_add_complement P I J
  rw [hP.2] at hid
  linarith

/-- Every cut receives its scaled demand, including zero and negative demands. -/
theorem scaled_cut_demand_le_of_subset_discrepancy {m n g : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hgm : g ∣ m) (hgn : g ∣ n)
    {P : Board m n} (hP : IsProbability P) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdev : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ t*(g : ℝ)/((m : ℝ)*n))
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    (1-t)*((I.card : ℝ)/m + (J.card : ℝ)/n - 1) ≤ cutMass P I J := by
  by_cases hp : 0 < (I.card : ℝ)/m + (J.card : ℝ)/n - 1
  · have hg := positive_rectangular_cut_grid hm hn hgm hgn hp
    have hb := cutMass_lower_of_subset_discrepancy hP I J (hdev I J)
    have hmul := mul_le_mul_of_nonneg_left hg ht
    rw [← mul_div_assoc] at hmul
    nlinarith
  · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) (le_of_not_gt hp)).trans
      (cutMass_nonneg hP.1 I J)

/-- Cut mass is homogeneous even for signed matrices and scalars. -/
theorem cutMass_smul {m n : ℕ} (P : Board m n) (a : ℝ)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass (a • P) I J = a * cutMass P I J := by
  simp [cutMass, Finset.mul_sum]

/-- Marginal discrepancy supplies the actual cuts of the rescaled capacity. -/
theorem rectangularTransportCuts_of_subset_discrepancy {m n g : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hgm : g ∣ m) (hgn : g ∣ n)
    {P : Board m n} (hP : IsProbability P) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hdev : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ t*(g : ℝ)/((m : ℝ)*n)) :
    RectangularTransportCuts ((1/(1-t)) • P) := by
  intro I J
  rw [cutMass_smul, one_div_mul_eq_div]
  apply (le_div_iff₀ (sub_pos.mpr ht1)).mpr
  simpa only [mul_comm] using
    scaled_cut_demand_le_of_subset_discrepancy hm hn hgm hgn hP ht ht1.le hdev I J

/-- A balanced probability matrix is genuinely constructed below P/(1-t).
The input concerns only actual marginal subsets; no desired cut is assumed. -/
theorem exists_balanced_dominated_of_subset_discrepancy {m n g : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hgm : g ∣ m) (hgn : g ∣ n)
    {P : Board m n} (hP : IsProbability P) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hdev : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ t*(g : ℝ)/((m : ℝ)*n)) :
    ∃ B : Board m n, IsProbability B ∧
      (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      ∀ i j, (1-t)*B i j ≤ P i j := by
  have hq : 0 < 1-t := sub_pos.mpr ht1
  have hnonneg : ∀ i j, 0 ≤ ((1/(1-t)) • P) i j := by
    intro i j
    exact mul_nonneg (div_nonneg (by norm_num) hq.le) (hP.1 i j)
  obtain ⟨B,hB⟩ := exists_rectangularTransport_of_cuts hm hn _ hnonneg
    (rectangularTransportCuts_of_subset_discrepancy hm hn hgm hgn hP ht ht1 hdev)
  refine ⟨B,hB.isProbability hm,hB.2.2.1,hB.2.2.2,?_⟩
  intro i j
  have h := hB.2.1 i j
  change B i j ≤ (1/(1-t))*P i j at h
  rw [one_div_mul_eq_div] at h
  simpa only [mul_comm] using (le_div_iff₀ hq).mp h

/-- Divisor-one interface, without any arithmetic refinement hypothesis. -/
theorem exists_balanced_dominated_of_subset_discrepancy_one {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P : Board m n} (hP : IsProbability P)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hdev : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ t/((m : ℝ)*n)) :
    ∃ B : Board m n, IsProbability B ∧
      (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      ∀ i j, (1-t)*B i j ≤ P i j := by
  apply exists_balanced_dominated_of_subset_discrepancy hm hn (one_dvd m) (one_dvd n)
    hP ht ht1
  simpa only [Nat.cast_one, mul_one] using hdev

/-- The gcd form retains the sharper cut grid at no additional hypothesis. -/
theorem exists_balanced_dominated_of_subset_discrepancy_gcd {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P : Board m n} (hP : IsProbability P)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hdev : ∀ (I : Finset (Fin m)) (J : Finset (Fin n)),
      |(∑ i ∈ I, rowSum P i) - (I.card : ℝ)/m| +
      |(∑ j ∈ J, colSum P j) - (J.card : ℝ)/n| ≤ t*(Nat.gcd m n : ℝ)/((m : ℝ)*n)) :
    ∃ B : Board m n, IsProbability B ∧
      (∀ i, rowSum B i = 1/(m : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      ∀ i j, (1-t)*B i j ≤ P i j :=
  exists_balanced_dominated_of_subset_discrepancy hm hn
    (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n) hP ht ht1 hdev

/-- Positive scaling retains every zero of the original probability matrix. -/
theorem scaled_balanced_zero_of_zero {m n : ℕ} {P B : Board m n}
    (hB : ∀ i j, 0 ≤ B i j) {t : ℝ} (ht1 : t < 1)
    (hdom : ∀ i j, (1-t)*B i j ≤ P i j) (i : Fin m) (j : Fin n)
    (hz : P i j = 0) : B i j = 0 := by
  apply le_antisymm _ (hB i j)
  have h := hdom i j
  rw [hz] at h
  exact nonpos_of_mul_nonpos_right h (sub_pos.mpr ht1)

end DittertRybin
