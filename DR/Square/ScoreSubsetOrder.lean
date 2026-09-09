import DR.Square.ScoreOrder

/-! Ordered score cuts retain marginal mass orientation at every cardinality. -/

namespace DittertRybin
open scoped BigOperators

theorem ordered_subset_sum_le_card {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hsum : ∑ i, r i = n) (I : Finset (Fin n))
    (horder : ∀ i ∈ I, ∀ j ∈ Iᶜ, r i ≤ r j) :
    ∑ i ∈ I, r i ≤ I.card := by
  have hh := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => horder i hi j hj
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hh
  have hcomp := Finset.sum_add_sum_compl I r
  rw [hsum] at hcomp
  have hcard : (Iᶜ.card : ℝ) + I.card = n := by
    have hnat : Iᶜ.card + I.card = n := by
      rw [Finset.card_compl]
      have hle := Finset.card_le_univ I
      simp only [Fintype.card_fin] at *
      omega
    exact_mod_cast hnat
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem ordered_subset_sum_ge_card {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hsum : ∑ i, r i = n) (I : Finset (Fin n))
    (horder : ∀ i ∈ I, ∀ j ∈ Iᶜ, r j ≤ r i) :
    (I.card : ℝ) ≤ ∑ i ∈ I, r i := by
  have hh := ordered_subset_sum_le_card hn r hsum Iᶜ
    (by intro i hi j hj; exact horder j (by simpa using hj) i hi)
  have hcomp := Finset.sum_add_sum_compl I r
  rw [hsum] at hcomp
  have hcard : (Iᶜ.card : ℝ) + I.card = n := by
    have hnat : Iᶜ.card + I.card = n := by
      rw [Finset.card_compl]
      have hle := Finset.card_le_univ I
      simp only [Fintype.card_fin] at *
      omega
    exact_mod_cast hnat
  linarith

theorem lower_score_cut_marginal_sums {n : ℕ} (hn : 0 < n)
    (A : Board n n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hmass : totalMass A = n) (S : Finset (SquareVertices n))
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β v ≤ squareStationaryScore A α β w) :
    (∑ i ∈ S.toLeft, rowSum A i) ≤ S.toLeft.card ∧
      (S.toRight.card : ℝ) ≤ ∑ j ∈ S.toRight, colSum A j := by
  constructor
  · apply ordered_subset_sum_le_card hn (rowSum A) hmass
    intro i hi j hj
    apply (squareStationaryScore_row_le_iff A α β hα hr i j).mp
    apply horder (.inl i) (by simpa using hi) (.inl j) (by simpa using hj)
  · apply ordered_subset_sum_ge_card hn (colSum A)
      (by rwa [← totalMass_eq_sum_colSum])
    intro i hi j hj
    apply (squareStationaryScore_col_le_iff A α β hβ hc i j).mp
    apply horder (.inr i) (by simpa using hi) (.inr j) (by simpa using hj)

theorem upper_score_cut_marginal_sums {n : ℕ} (hn : 0 < n)
    (A : Board n n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (hmass : totalMass A = n) (S : Finset (SquareVertices n))
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β w ≤ squareStationaryScore A α β v) :
    (S.toLeft.card : ℝ) ≤ (∑ i ∈ S.toLeft, rowSum A i) ∧
      (∑ j ∈ S.toRight, colSum A j) ≤ S.toRight.card := by
  constructor
  · apply ordered_subset_sum_ge_card hn (rowSum A) hmass
    intro i hi j hj
    apply (squareStationaryScore_row_le_iff A α β hα hr j i).mp
    apply horder (.inl i) (by simpa using hi) (.inl j) (by simpa using hj)
  · apply ordered_subset_sum_le_card hn (colSum A)
      (by rwa [← totalMass_eq_sum_colSum])
    intro i hi j hj
    apply (squareStationaryScore_col_le_iff A α β hβ hc j i).mp
    apply horder (.inr i) (by simpa using hi) (.inr j) (by simpa using hj)

end DittertRybin
