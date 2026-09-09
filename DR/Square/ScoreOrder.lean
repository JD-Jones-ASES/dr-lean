import DR.Square.SpectralPair

/-! Exact marginal-order information retained by the stationary spectral score. -/

namespace DittertRybin

open scoped BigOperators

/-- The fractional score is strictly order preserving on positive marginals. -/
theorem fractional_score_le_iff {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    a * (x - 1) / x ≤ a * (y - 1) / y ↔ x ≤ y := by
  rw [div_le_div_iff₀ hx hy]
  constructor
  · intro h
    have hh : a * x ≤ a * y := by nlinarith
    exact (mul_le_mul_iff_right₀ ha).mp (by simpa only [mul_comm] using hh)
  · intro h
    have hh := mul_le_mul_of_nonneg_left h ha.le
    nlinarith

theorem squareStationaryScore_row_le_iff {n : ℕ} (A : Board n n) (α β : ℝ)
    (ha : 0 < α) (hr : ∀ i, 0 < rowSum A i) (i k : Fin n) :
    squareStationaryScore A α β (.inl i) ≤ squareStationaryScore A α β (.inl k) ↔
      rowSum A i ≤ rowSum A k :=
  fractional_score_le_iff (Real.sqrt_pos.mpr ha) (hr i) (hr k)

theorem squareStationaryScore_col_le_iff {n : ℕ} (A : Board n n) (α β : ℝ)
    (hb : 0 < β) (hc : ∀ j, 0 < colSum A j) (j l : Fin n) :
    squareStationaryScore A α β (.inr j) ≤ squareStationaryScore A α β (.inr l) ↔
      colSum A l ≤ colSum A j := by
  change -Real.sqrt β * (colSum A j - 1) / colSum A j ≤
    -Real.sqrt β * (colSum A l - 1) / colSum A l ↔ _
  simp only [neg_mul, neg_div, neg_le_neg_iff]
  exact fractional_score_le_iff (Real.sqrt_pos.mpr hb) (hc l) (hc j)

/-- A singleton row/column lower score cut picks a minimum row and maximum column. -/
theorem singleton_lower_score_cut_extrema {n : ℕ} (A : Board n n) (α β : ℝ)
    (ha : 0 < α) (hb : 0 < β) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (S : Finset (SquareVertices n)) (i j : Fin n) (hL : S.toLeft = {i}) (hR : S.toRight = {j})
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β v ≤ squareStationaryScore A α β w) :
    (∀ r, rowSum A i ≤ rowSum A r) ∧ (∀ c, colSum A c ≤ colSum A j) := by
  have hi : Sum.inl i ∈ S := by simp [← Finset.mem_toLeft, hL]
  have hj : Sum.inr j ∈ S := by simp [← Finset.mem_toRight, hR]
  constructor
  · intro r
    by_cases hri : r = i
    · subst r; exact le_rfl
    · apply (squareStationaryScore_row_le_iff A α β ha hr i r).mp
      apply horder _ hi _
      simp [← Finset.mem_toLeft, hL, hri]
  · intro c
    by_cases hcj : c = j
    · subst c; exact le_rfl
    · apply (squareStationaryScore_col_le_iff A α β hb hc j c).mp
      apply horder _ hj _
      simp [← Finset.mem_toRight, hR, hcj]

/-- A singleton complemented prefix has the opposite extremal orientation. -/
theorem singleton_upper_score_cut_extrema {n : ℕ} (A : Board n n) (α β : ℝ)
    (ha : 0 < α) (hb : 0 < β) (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (S : Finset (SquareVertices n)) (i j : Fin n) (hL : S.toLeft = {i}) (hR : S.toRight = {j})
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β w ≤ squareStationaryScore A α β v) :
    (∀ r, rowSum A r ≤ rowSum A i) ∧ (∀ c, colSum A j ≤ colSum A c) := by
  have hi : Sum.inl i ∈ S := by simp [← Finset.mem_toLeft, hL]
  have hj : Sum.inr j ∈ S := by simp [← Finset.mem_toRight, hR]
  constructor
  · intro r
    by_cases hri : r = i
    · subst r; exact le_rfl
    · apply (squareStationaryScore_row_le_iff A α β ha hr r i).mp
      apply horder _ hi _
      simp [← Finset.mem_toLeft, hL, hri]
  · intro c
    by_cases hcj : c = j
    · subst c; exact le_rfl
    · apply (squareStationaryScore_col_le_iff A α β hb hc c j).mp
      apply horder _ hj _
      simp [← Finset.mem_toRight, hR, hcj]

end DittertRybin
