import DR.Square.OrderThree

/-!
# Positive order-three maximizers

Three explicit flat column blends replace the limiting symmetrization argument.
The stationary marginal equations determine the averaged board, and an exact
three-dimensional comparison matrix recovers the original board.
-/

open scoped BigOperators
open Finset

namespace DittertRybin

theorem blendThreeColumns_pos {A : Board 3 3} (hA : ∀ i j, 0 < A i j)
    (j k : Fin 3) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∀ i l, 0 < blendThreeColumns A j k t i l := by
  intro i l
  have hcomb (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < (1 - t) * a + t * b := by
    by_cases heq : t = 1
    · simpa [heq] using hb
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 heq)) ha)
        (mul_nonneg ht.1 hb.le)
  unfold blendThreeColumns
  split_ifs
  · exact hcomb _ _ (hA i j) (hA i k)
  · simpa [add_comm] using hcomb _ _ (hA i k) (hA i j)
  · exact hA i l

theorem orderThree_positive_blend_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 < A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (j k : Fin 3) (hjk : j ≠ k) (t : ℝ) :
    ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (blendThreeColumns A j k t) := by
  rw [dittert_three_same_support_blend_flat (fun i j => (hA i j).le) hmass hmax j k hjk
    (fun i => ⟨fun _ => hA i k, fun _ => hA i j⟩)]
  exact hmax

/-- Equal columns at an actual maximizer force every row and column marginal to one. -/
theorem orderThree_equal_columns_globalMax_uniform {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (heq : ∀ i j, A i j = A i 0) : A = uniformDittertMatrix 3 := by
  have hcols (j : Fin 3) : colSum A j = colSum A 0 := by simp [colSum, heq]
  have hc0 : colSum A 0 = 1 := by
    rw [totalMass_eq_sum_colSum] at hmass
    simp only [hcols, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmass
    norm_num at hmass
    linarith
  have hc (j : Fin 3) : colSum A j = 1 := (hcols j).trans hc0
  have hcont := dittert_globalMax_isContender (by decide : 0 < 3) A hmax
  have hpos := (dittert_contender_stationary_coefficients_pos (by decide : 2 ≤ 3) A hA hmass hcont).1
  have hstationary := (dittert_globalMax_stationary_pair (by decide : 2 ≤ 3) A hA hmass hmax).1
  have hr (i : Fin 3) : rowSum A i = 1 := by
    have h := hstationary i
    simp only [hc, sub_self, mul_zero, zero_div, Finset.sum_const_zero, neg_zero] at h hpos
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hpos.ne')
  ext i j
  have hi := hr i
  simp only [rowSum, heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
  norm_num at hi
  rw [heq]
  norm_num [uniformDittertMatrix]
  linarith

/-- With the remaining column uniform, the exact column-comparison matrix is
diag(1) with off-diagonal entries 2/3. Its kernel is zero. -/
theorem orderThree_uniform_third_column_equal_pair {A : Board 3 3}
    (hA : ∀ i j, 0 < A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hthird : ∀ i, A i l = 1 / 3) : ∀ i, A i j = A i k := by
  have hC (i h : Fin 3) : orderThreeColumnComparison A j k i h =
      if i = h then 1 else 2 / 3 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [orderThreeColumnComparison, orderThreeRemainingRow, Fin.sum_univ_succ] <;> norm_num
  have h (i : Fin 3) := orderThree_column_comparison_eq_zero
    (fun i j => (hA i j).le) hmass hmax i j k hjk (hA i j) (hA i k)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [hC, Fin.sum_univ_succ] at h0 h1 h2
  norm_num [Fin.ext_iff] at h0 h1 h2
  intro i
  fin_cases i
  · change A 0 j = A 0 k
    linarith only [h0, h1, h2]
  · change A 1 j = A 1 k
    linarith only [h0, h1, h2]
  · change A 2 j = A 2 k
    linarith only [h0, h1, h2]

/-- Three exact finite blends give every column the original row mean. -/
theorem orderThree_three_blends (A : Board 3 3) :
    blendThreeColumns (blendThreeColumns (blendThreeColumns A 0 1 (1 / 2)) 0 2 (1 / 3))
      1 2 (1 / 2) = fun i _ => rowSum A i / 3 := by
  ext i j
  fin_cases j <;> simp [blendThreeColumns, rowSum, Fin.sum_univ_succ] <;> ring

/-- Every strictly positive order-three global maximizer is the uniform matrix. -/
theorem orderThree_positive_globalMax_uniform {A : Board 3 3}
    (hA : ∀ i j, 0 < A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix 3 := by
  let A1 := blendThreeColumns A 0 1 (1 / 2)
  let A2 := blendThreeColumns A1 0 2 (1 / 3)
  let A3 := blendThreeColumns A2 1 2 (1 / 2)
  have hp1 := blendThreeColumns_pos hA 0 1 (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)
  have hm1 : totalMass A1 = 3 := (blendThreeColumns_feasible
    (fun i j => (hA i j).le) 0 1 (by decide) (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)).2.trans hmass
  have hg1 := orderThree_positive_blend_globalMax hA hmass hmax 0 1 (by decide) (1 / 2)
  have hp2 := blendThreeColumns_pos hp1 0 2 (by norm_num : (1 / 3 : ℝ) ∈ Set.Icc 0 1)
  have hm2 : totalMass A2 = 3 := (blendThreeColumns_feasible
    (fun i j => (hp1 i j).le) 0 2 (by decide) (by norm_num : (1 / 3 : ℝ) ∈ Set.Icc 0 1)).2.trans hm1
  have hg2 := orderThree_positive_blend_globalMax hp1 hm1 hg1 0 2 (by decide) (1 / 3)
  have hp3 := blendThreeColumns_pos hp2 1 2 (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)
  have hm3 : totalMass A3 = 3 := (blendThreeColumns_feasible
    (fun i j => (hp2 i j).le) 1 2 (by decide) (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)).2.trans hm2
  have hg3 := orderThree_positive_blend_globalMax hp2 hm2 hg2 1 2 (by decide) (1 / 2)
  have hmean : A3 = fun i _ => rowSum A i / 3 := orderThree_three_blends A
  have hu3 : A3 = uniformDittertMatrix 3 := orderThree_equal_columns_globalMax_uniform
    (fun i j => (hp3 i j).le) hm3 hg3 (by rw [hmean]; intros; rfl)
  have hc0 (i : Fin 3) : A2 i 0 = 1 / 3 := by
    have h := congrFun (congrFun hu3 i) 0
    simpa [A3, blendThreeColumns, uniformDittertMatrix] using h
  have heq2 := orderThree_uniform_third_column_equal_pair hp2 hm2 hg2 1 2 0
    (by decide) (by decide) (by decide) hc0
  have hu2 : A2 = uniformDittertMatrix 3 := by
    ext i j
    have h := congrFun (congrFun hu3 i) j
    have he := heq2 i
    change A2 i 1 = A2 i 2 at he
    norm_num [uniformDittertMatrix]
    fin_cases j
    · exact hc0 i
    · change A2 i 1 = 1 / 3
      norm_num [A3, blendThreeColumns, uniformDittertMatrix, Fin.ext_iff] at h
      linarith only [he, h]
    · change A2 i 2 = 1 / 3
      norm_num [A3, blendThreeColumns, uniformDittertMatrix, Fin.ext_iff] at h
      linarith only [he, h]
  have hu1 : A1 = uniformDittertMatrix 3 := by
    ext i j
    have h0 := congrFun (congrFun hu2 i) 0
    have h1 := congrFun (congrFun hu2 i) 1
    have h2 := congrFun (congrFun hu2 i) 2
    norm_num [A2, blendThreeColumns, uniformDittertMatrix, Fin.ext_iff] at h0 h1 h2 ⊢
    fin_cases j
    · change A1 i 0 = 1 / 3
      linarith only [h0, h2]
    · exact h1
    · change A1 i 2 = 1 / 3
      linarith only [h0, h2]
  have hc2 (i : Fin 3) : A i 2 = 1 / 3 := by
    have h := congrFun (congrFun hu1 i) 2
    simpa [A1, blendThreeColumns, uniformDittertMatrix] using h
  have heq0 := orderThree_uniform_third_column_equal_pair hA hmass hmax 0 1 2
    (by decide) (by decide) (by decide) hc2
  ext i j
  have h := congrFun (congrFun hu1 i) j
  have he := heq0 i
  fin_cases j <;> norm_num [A1, blendThreeColumns, uniformDittertMatrix, Fin.ext_iff] at h ⊢ <;> linarith

end DittertRybin
