import DR.Endpoint.RowCollisionLocalized
import Mathlib.Algebra.BigOperators.Fin

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

-- Exact unordered counts: one remaining pair for a triple involving a fixed row,
-- and three partitions into two pairs involving a fixed row of a four-row set.
example : (rowPairsOutside (0:Fin 3)).card=1 := by decide +kernel
example : (∑ e ∈ rowCollisionIncident (0:Fin 4), (rowPairsDisjoint e).card)=3 := by decide +kernel

-- The pair identity includes negative coordinates and has the exact factor two.
example : (∑ e : SampleIndexPair 2, (![-1,2] : Fin 2 → ℝ) e.val.1*(![-1,2] : Fin 2 → ℝ) e.val.2)= -2 := by
  have h := sum_rowPair_products_identity (![-1,2] : Fin 2 → ℝ)
  norm_num [Fin.sum_univ_two] at h
  linarith
example : (∑ _e : SampleIndexPair 3, (1:ℝ)*1)=3 := by
  norm_num [card_sampleIndexPair]
example : (∑ _e : SampleIndexPair 3, (1:ℝ)*1) ≠ 6 := by
  norm_num [card_sampleIndexPair]

-- A literal column cap alone supplies the local-lemma threshold and yields
-- the exact rational localized deficit-two bound for four rows.
example {n : ℕ} (X : Board 4 n) (hX : ∀ i j, 0 ≤ X i j)
    (hs : ∀ i, rowSum X i=1) (hc : ∀ j, colSum X j ≤ 1/32) (i : Fin 4) :
    rowLocalizedDeficitTwoLoad X i ≤ 19/2592 := by
  have hd (h : Fin 4) : rowCollisionLoad X h ≤ 1/8 :=
    (rowCollisionLoad_le_column_cap X hX hs hc h).trans (by norm_num)
  have h := rowLocalizedDeficitTwoLoad_le_columnCap X hX hs hd (1/32) hc i
  norm_num at h
  exact h

-- With zero collision loads the actual normalized exact-pattern penalties vanish.
example {m n : ℕ} (X : Board m n) (hX : ∀ i j, 0 ≤ X i j)
    (hs : ∀ i, rowSum X i=1) (hz : ∀ i, rowCollisionLoad X i=0)
    (hc : ∀ j, colSum X j ≤ 1) (i : Fin m) : rowLocalizedDeficitTwoLoad X i=0 := by
  have hd (h : Fin m) : rowCollisionLoad X h ≤ 1/8 := by rw [hz h]; norm_num
  have h := rowLocalizedDeficitTwoLoad_le X hX hs hd 1 hc i
  rw [hz i,zero_mul] at h
  apply le_antisymm h
  have hp0 := rowAvoidance_nonneg X hX
  unfold rowLocalizedDeficitTwoLoad rowLocalizedTripletonLoad rowLocalizedTwoDoubletonsLoad
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro e he
    exact div_nonneg (rowAssignmentEvent_nonneg X hX _) hp0
  · apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro f hf
    exact div_nonneg (rowAssignmentEvent_nonneg X hX _) hp0

-- No row exists in the empty model; its complete localized load sums are zero.
example : (∑ i : Fin 0, rowLocalizedDeficitTwoLoad (0 : Board 0 0) i)=0 := by simp

#print axioms sum_rowPair_incidence
#print axioms sum_rowPair_products_identity
#print axioms sum_rowPairsOutside_product_le
#print axioms rowLocalizedDoubletonLoad_le
#print axioms rowTripleton_moment_sum_le
#print axioms rowLocalizedTripletonLoad_le
#print axioms rowLocalizedTwoDoubletonsLoad_le
#print axioms rowLocalizedDeficitTwoLoad_le
#print axioms rowLocalizedDeficitTwoLoad_le_columnCap

end DittertRybin.Tests
