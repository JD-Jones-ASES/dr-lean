import DR.Square.ScoreSubsetOrder

/-! Full marginal ordering retained by a stationary score prefix. -/

namespace DittertRybin
open scoped BigOperators

/-- Chosen rows are the smallest rows and chosen columns the largest columns,
with all ties allowed. -/
def LowerMarginalCut {n : ℕ} (A : Board n n) (I J : Finset (Fin n)) : Prop :=
  (∀ i ∈ I, ∀ r ∈ Iᶜ, rowSum A i ≤ rowSum A r) ∧
  (∀ j ∈ J, ∀ c ∈ Jᶜ, colSum A c ≤ colSum A j)

theorem lower_score_cut_order {n : ℕ}
    (A : Board n n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (S : Finset (SquareVertices n))
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β v ≤ squareStationaryScore A α β w) :
    LowerMarginalCut A S.toLeft S.toRight := by
  constructor
  · intro i hi r hrS
    apply (squareStationaryScore_row_le_iff A α β hα hr i r).mp
    exact horder (.inl i) (by simpa using hi) (.inl r) (by simpa using hrS)
  · intro j hj c hcS
    apply (squareStationaryScore_col_le_iff A α β hβ hc j c).mp
    exact horder (.inr j) (by simpa using hj) (.inr c) (by simpa using hcS)

/-- The opposite score orientation becomes a lower marginal cut after transposition. -/
theorem upper_score_cut_order {n : ℕ}
    (A : Board n n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hr : ∀ i, 0 < rowSum A i) (hc : ∀ j, 0 < colSum A j)
    (S : Finset (SquareVertices n))
    (horder : ∀ v ∈ S, ∀ w ∈ Sᶜ, squareStationaryScore A α β w ≤ squareStationaryScore A α β v) :
    LowerMarginalCut A.transpose S.toRight S.toLeft := by
  constructor
  · intro j hj c hcS
    change colSum A j ≤ colSum A c
    apply (squareStationaryScore_col_le_iff A α β hβ hc c j).mp
    exact horder (.inr j) (by simpa using hj) (.inr c) (by simpa using hcS)
  · intro i hi r hrS
    change rowSum A r ≤ rowSum A i
    apply (squareStationaryScore_row_le_iff A α β hα hr r i).mp
    exact horder (.inl i) (by simpa using hi) (.inl r) (by simpa using hrS)

theorem LowerMarginalCut.mass_orientation {n : ℕ} (hn : 0 < n)
    {A : Board n n} {I J : Finset (Fin n)} (h : LowerMarginalCut A I J)
    (hmass : totalMass A = n) :
    (∑ i ∈ I, rowSum A i) ≤ I.card ∧ (J.card : ℝ) ≤ ∑ j ∈ J, colSum A j :=
  ⟨ordered_subset_sum_le_card hn _ hmass I h.1,
    ordered_subset_sum_ge_card hn _ (by rwa [← totalMass_eq_sum_colSum]) J h.2⟩

/-- Each complementary row is at least the mean of all chosen rows. -/
theorem LowerMarginalCut.complementary_row_floor {n : ℕ}
    {A : Board n n} {I J : Finset (Fin n)} (h : LowerMarginalCut A I J)
    (hI : 0 < I.card) (r : Fin n) (hr : r ∈ Iᶜ) :
    (∑ i ∈ I, rowSum A i) / I.card ≤ rowSum A r := by
  apply (div_le_iff₀ (by exact_mod_cast hI : 0 < (I.card : ℝ))).mpr
  have hs := Finset.sum_le_sum fun i hi => h.1 i hi r hr
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

/-- Each chosen column is at least the mean of the complementary columns. -/
theorem LowerMarginalCut.chosen_col_floor {n : ℕ}
    {A : Board n n} {I J : Finset (Fin n)} (h : LowerMarginalCut A I J)
    (hJ : 0 < Jᶜ.card) (j : Fin n) (hj : j ∈ J) :
    (∑ c ∈ Jᶜ, colSum A c) / Jᶜ.card ≤ colSum A j := by
  apply (div_le_iff₀ (by exact_mod_cast hJ : 0 < (Jᶜ.card : ℝ))).mpr
  have hs := Finset.sum_le_sum fun c hc => h.2 j hj c hc
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

end DittertRybin
