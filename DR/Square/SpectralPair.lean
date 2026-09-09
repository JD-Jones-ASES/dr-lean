import DR.Square.NormalizedMatrix
import DR.Square.WeightedSweep
import DR.Square.CapacityEquality

/-!
# The explicit reversible pair arising from square stationarity

Vertices are rows and columns. Their weights are the marginals divided by
2n and their crossing conductances are the actual cell masses divided by
2n. The score constructed from the two stationary equations is a genuine
weighted eigenfunction. The construction allows disconnected support.
-/

namespace DittertRybin

open scoped BigOperators

abbrev SquareVertices (n : ℕ) := Fin n ⊕ Fin n

noncomputable def squareVertexWeight {n : ℕ} (A : Board n n) : SquareVertices n → ℝ
  | .inl i => rowSum A i / (2 * n)
  | .inr j => colSum A j / (2 * n)

noncomputable def squareConductance {n : ℕ} (A : Board n n) :
    SquareVertices n → SquareVertices n → ℝ
  | .inl i, .inr j => A i j / (2 * n)
  | .inr j, .inl i => A i j / (2 * n)
  | _, _ => 0

noncomputable def squareStationaryScore {n : ℕ} (A : Board n n) (α β : ℝ) :
    SquareVertices n → ℝ
  | .inl i => Real.sqrt α * (rowSum A i - 1) / rowSum A i
  | .inr j => -Real.sqrt β * (colSum A j - 1) / colSum A j

theorem squareVertexWeight_pos {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j) (v : SquareVertices n) :
    0 < squareVertexWeight A v := by
  cases v with
  | inl i => exact div_pos (hr i) (by positivity)
  | inr j => exact div_pos (hc j) (by positivity)

theorem squareVertexWeight_sum {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hmass : totalMass A = n) : (∑ v, squareVertexWeight A v) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Fintype.sum_sum_type]
  simp only [squareVertexWeight, ← Finset.sum_div]
  rw [← totalMass, ← totalMass_eq_sum_colSum, hmass]
  field_simp
  norm_num

theorem squareConductance_nonneg {n : ℕ} (A : Board n n) (hA : ∀ i j, 0 ≤ A i j)
    (v w : SquareVertices n) : 0 ≤ squareConductance A v w := by
  cases v <;> cases w <;> simp only [squareConductance]
  all_goals first | exact le_rfl | exact div_nonneg (hA _ _) (by positivity)

theorem squareConductance_symm {n : ℕ} (A : Board n n) (v w : SquareVertices n) :
    squareConductance A v w = squareConductance A w v := by
  cases v <;> cases w <;> rfl

/-- The conductance row sums equal the prescribed vertex weights. -/
theorem squareConductance_sum {n : ℕ} (A : Board n n) (v : SquareVertices n) :
    (∑ w, squareConductance A v w) = squareVertexWeight A v := by
  cases v <;> simp [Fintype.sum_sum_type, squareConductance, squareVertexWeight,
    ← Finset.sum_div, rowSum, colSum]

theorem squareStationaryScore_mean_zero {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hmass : totalMass A = n) (α β : ℝ) :
    (∑ v, squareVertexWeight A v * squareStationaryScore A α β v) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hrow (i : Fin n) : squareVertexWeight A (.inl i) * squareStationaryScore A α β (.inl i) =
      (Real.sqrt α / (2 * n)) * (rowSum A i - 1) := by
    dsimp [squareVertexWeight, squareStationaryScore]
    field_simp [(hr i).ne']
  have hcol (j : Fin n) : squareVertexWeight A (.inr j) * squareStationaryScore A α β (.inr j) =
      (-Real.sqrt β / (2 * n)) * (colSum A j - 1) := by
    dsimp [squareVertexWeight, squareStationaryScore]
    field_simp [(hc j).ne']
  rw [Fintype.sum_sum_type]
  simp_rw [hrow, hcol, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← totalMass, ← totalMass_eq_sum_colSum, hmass]
  simp

/-- The two exact stationarity equations produce the weighted eigenfunction directly. -/
theorem squareStationaryScore_eigen {n : ℕ} (A : Board n n) (α β : ℝ)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hrow : ∀ i, α * (rowSum A i - 1) = -(∑ j, A i j * (colSum A j - 1) / colSum A j))
    (hcol : ∀ j, β * (colSum A j - 1) = -(∑ i, A i j * (rowSum A i - 1) / rowSum A i))
    (v : SquareVertices n) :
    (∑ w, squareConductance A v w * squareStationaryScore A α β w) =
      (Real.sqrt α * Real.sqrt β) * squareVertexWeight A v * squareStationaryScore A α β v := by
  cases v with
  | inl i =>
    rw [Fintype.sum_sum_type]
    simp only [squareConductance, squareStationaryScore, zero_mul, Finset.sum_const_zero, zero_add,
      squareVertexWeight]
    have hterm (j : Fin n) : A i j / (2 * n) * (-Real.sqrt β * (colSum A j - 1) / colSum A j) =
        (-Real.sqrt β / (2 * n)) * (A i j * (colSum A j - 1) / colSum A j) := by ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hs := hrow i
    have heq : (∑ j, A i j * (colSum A j - 1) / colSum A j) = -α * (rowSum A i - 1) := by linarith
    rw [heq]
    field_simp [(hr i).ne']
    rw [Real.sq_sqrt ha]
    ring
  | inr j =>
    rw [Fintype.sum_sum_type]
    simp only [squareConductance, squareStationaryScore, zero_mul, Finset.sum_const_zero, add_zero,
      squareVertexWeight]
    have hterm (i : Fin n) : A i j / (2 * n) * (Real.sqrt α * (rowSum A i - 1) / rowSum A i) =
        (Real.sqrt α / (2 * n)) * (A i j * (rowSum A i - 1) / rowSum A i) := by ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hs := hcol j
    have heq : (∑ i, A i j * (rowSum A i - 1) / rowSum A i) = -β * (colSum A j - 1) := by linarith
    rw [heq]
    field_simp [(hc j).ne']
    rw [Real.sq_sqrt hb]
    ring

/-- Exact Dirichlet-energy identity for a finite reversible weighted eigenfunction. -/
theorem sweepEnergy_nonneg {ι : Type*} [Fintype ι]
    (c : ι → ι → ℝ) (hc : ∀ v w, 0 ≤ c v w) (f : ι → ℝ) : 0 ≤ sweepEnergy c f := by
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => mul_nonneg (hc v w) (sq_nonneg _))

/-- Exact Dirichlet-energy identity for a finite reversible weighted eigenfunction. -/
theorem sweepEnergy_eq_gap_mul_variance {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (c : ι → ι → ℝ) (lam : ℝ)
    (hsym : ∀ v w, c v w = c w v) (hrow : ∀ v, (∑ w, c v w) = π v)
    (heig : ∀ v, (∑ w, c v w * f w) = lam * π v * f v)
    (hmean : sweepMean π f = 0) : sweepEnergy c f = (1 - lam) * sweepVariance π f := by
  have hleft : (∑ v, ∑ w, c v w * f v ^ 2) = ∑ v, π v * f v ^ 2 := by
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_mul, hrow]
  have hright : (∑ v, ∑ w, c v w * f w ^ 2) = ∑ v, π v * f v ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [hsym _ w]
    rw [← Finset.sum_mul, hrow]
  have hcross : (∑ v, ∑ w, c v w * f v * f w) = lam * ∑ v, π v * f v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    calc
      _ = f v * (∑ w, c v w * f w) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [heig]; ring
  have hpoint (v w : ι) : c v w * (f v - f w) ^ 2 =
      c v w * f v ^ 2 + c v w * f w ^ 2 - 2 * (c v w * f v * f w) := by ring
  unfold sweepEnergy
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hleft, hright, hcross]
  simp only [sweepVariance, hmean, sub_zero]
  ring

/-- The constructed score has exactly the claimed spectral energy, even if it vanishes. -/
theorem squareStationaryScore_energy {n : ℕ} (hn : 0 < n) (A : Board n n) (α β : ℝ)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hmass : totalMass A = n)
    (hrow : ∀ i, α * (rowSum A i - 1) = -(∑ j, A i j * (colSum A j - 1) / colSum A j))
    (hcol : ∀ j, β * (colSum A j - 1) = -(∑ i, A i j * (rowSum A i - 1) / rowSum A i)) :
    sweepEnergy (squareConductance A) (squareStationaryScore A α β) =
      (1 - Real.sqrt α * Real.sqrt β) *
        sweepVariance (squareVertexWeight A) (squareStationaryScore A α β) := by
  apply sweepEnergy_eq_gap_mul_variance
  · exact squareConductance_symm A
  · exact squareConductance_sum A
  · exact squareStationaryScore_eigen A α β ha hb hr hc hrow hcol
  · exact squareStationaryScore_mean_zero hn A hr hc hmass α β

/-- A nonunit marginal gives a nonzero score and hence positive weighted variance. -/
theorem squareStationaryScore_variance_pos {n : ℕ} (hn : 0 < n) (A : Board n n) (α β : ℝ)
    (ha : 0 < α) (hb : 0 < β) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hmass : totalMass A = n)
    (hunbalanced : (∃ i, rowSum A i ≠ 1) ∨ (∃ j, colSum A j ≠ 1)) :
    0 < sweepVariance (squareVertexWeight A) (squareStationaryScore A α β) := by
  have hmean : sweepMean (squareVertexWeight A) (squareStationaryScore A α β) = 0 :=
    squareStationaryScore_mean_zero hn A hr hc hmass α β
  simp only [sweepVariance, hmean, sub_zero]
  have hex : ∃ v : SquareVertices n, squareStationaryScore A α β v ≠ 0 := by
    rcases hunbalanced with ⟨i, hi⟩ | ⟨j, hj⟩
    · refine ⟨.inl i, ?_⟩
      exact div_ne_zero (mul_ne_zero (Real.sqrt_pos.mpr ha).ne' (sub_ne_zero.mpr hi)) (hr i).ne'
    · refine ⟨.inr j, ?_⟩
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne')
        (sub_ne_zero.mpr hj)) (hc j).ne'
  obtain ⟨v, hv⟩ := hex
  apply lt_of_lt_of_le (mul_pos (squareVertexWeight_pos hn A hr hc v) (sq_pos_of_ne_zero hv))
  exact Finset.single_le_sum
    (fun w _ => mul_nonneg (squareVertexWeight_pos hn A hr hc w).le (sq_nonneg _))
    (Finset.mem_univ v)

noncomputable def dittertAlpha {n : ℕ} (A : Board n n) : ℝ :=
  ((∏ i, rowSum A i) - A.permanent) / (∏ j, colSum A j)

noncomputable def dittertBeta {n : ℕ} (A : Board n n) : ℝ :=
  ((∏ j, colSum A j) - A.permanent) / (∏ i, rowSum A i)

noncomputable def dittertSpectralScore {n : ℕ} (A : Board n n) : SquareVertices n → ℝ :=
  squareStationaryScore A (dittertAlpha A) (dittertBeta A)

noncomputable def dittertSpectralGap {n : ℕ} (A : Board n n) : ℝ :=
  1 - Real.sqrt (dittertAlpha A) * Real.sqrt (dittertBeta A)

/-- A balanced contender is uniform by the proved permanent inequality and equality case. -/
theorem dittert_contender_uniform_of_balanced {n : ℕ} (A : Board n n)
    (hA : ∀ i j, 0 ≤ A i j) (hr : ∀ i, rowSum A i = 1) (hc : ∀ j, colSum A j = 1)
    (hcont : 2 - dittertConstant n ≤ dittertFunctional A) : A = uniformDittertMatrix n := by
  have hDS : A ∈ doublyStochastic ℝ (Fin n) := mem_doublyStochastic_iff_sum.mpr ⟨hA, hr, hc⟩
  have hp := permanent_lower_bound_of_doublyStochastic hDS
  simp only [dittertFunctional, hr, hc, Finset.prod_const_one] at hcont
  have heq : A.permanent = dittertConstant n := by linarith
  have hu := uniform_of_permanent_eq_dittertConstant hDS heq
  ext i j
  exact hu i j

theorem dittert_globalMax_energy {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) :
    sweepEnergy (squareConductance A) (dittertSpectralScore A) =
      dittertSpectralGap A * sweepVariance (squareVertexWeight A) (dittertSpectralScore A) := by
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  obtain ⟨ha, hb⟩ := dittert_contender_stationary_coefficients_pos hn A hA hmass hcont
  obtain ⟨hrow, hcol⟩ := dittert_globalMax_stationary_pair hn A hA hmass hmax
  exact squareStationaryScore_energy (by omega) A (dittertAlpha A) (dittertBeta A)
    ha.le hb.le hr hc hmass hrow hcol

theorem dittert_globalMax_variance_pos {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix n) :
    0 < sweepVariance (squareVertexWeight A) (dittertSpectralScore A) := by
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos hn A hA hmass hcont
  obtain ⟨ha, hb⟩ := dittert_contender_stationary_coefficients_pos hn A hA hmass hcont
  have hun : (∃ i, rowSum A i ≠ 1) ∨ (∃ j, colSum A j ≠ 1) := by
    by_contra h
    push Not at h
    exact hu (dittert_contender_uniform_of_balanced A hA h.1 h.2 hcont)
  exact squareStationaryScore_variance_pos (by omega) A (dittertAlpha A) (dittertBeta A)
    ha hb hr hc hmass hun

/-- The elementary product bound giving the precise spectral-gap upper bound. -/
theorem stationary_gap_upper_bound {R C p q : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hp : 0 ≤ p) (hq : 0 < q)
    (hqR : q ≤ R) (hqC : q ≤ C) (hpq : p < q) :
    1 - Real.sqrt ((R - p) / C) * Real.sqrt ((C - p) / R) ≤ p / q := by
  have hpr : p / R ≤ p / q := div_le_div_of_nonneg_left hp hq hqR
  have hpc : p / C ≤ p / q := div_le_div_of_nonneg_left hp hq hqC
  have hl : 0 ≤ 1 - p / q := by rw [sub_nonneg, div_le_one hq]; exact hpq.le
  have hxr : 1 - p / q ≤ 1 - p / R := by linarith
  have hxc : 1 - p / q ≤ 1 - p / C := by linarith
  have hprod : (1 - p / q) ^ 2 ≤ ((R - p) / C) * ((C - p) / R) := by
    have h := mul_le_mul hxr hxc hl (hl.trans hxr)
    have heq : (1 - p / R) * (1 - p / C) = ((R - p) / C) * ((C - p) / R) := by
      field_simp
    simpa only [← pow_two, heq] using h
  have hsqrt := Real.le_sqrt_of_sq_le hprod
  rw [Real.sqrt_mul (div_nonneg (by linarith) hC.le)] at hsqrt
  linarith

/-- Both endpoints of the spectral-gap bound include zero permanent and disconnected support. -/
theorem dittert_globalMax_gap_bounds {n : ℕ} (hn : 2 ≤ n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (hu : A ≠ uniformDittertMatrix n) :
    0 ≤ dittertSpectralGap A ∧
      dittertSpectralGap A ≤ A.permanent / (1 - (dittertConstant n - A.permanent)) := by
  have hcont := dittert_globalMax_isContender (by omega) A hmax
  obtain ⟨hR, hC⟩ := dittert_contender_products_pos hn A hA hmass hcont
  obtain ⟨hrho, hsigma, hb, hd0, hdg⟩ := dittert_contender_deficit_budget hn A hA hmass hcont
  have hp := permanent_nonneg hA
  have hg := dittertConstant_lt_one hn
  constructor
  · have hE : 0 ≤ sweepEnergy (squareConductance A) (dittertSpectralScore A) :=
      sweepEnergy_nonneg _ (squareConductance_nonneg A hA) _
    rw [dittert_globalMax_energy hn A hA hmass hmax] at hE
    exact nonneg_of_mul_nonneg_left hE (dittert_globalMax_variance_pos hn A hA hmass hmax hu)
  · apply stationary_gap_upper_bound hR hC hp (by linarith)
    · linarith
    · linarith
    · linarith

end DittertRybin
