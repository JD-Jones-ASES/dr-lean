import DR.Square.OrderThreeCanonical

/-! Finite support-preserving averages reduce actual zero faces to their
stationary canonical matrices. No compact face minimizer is assumed. -/

namespace DittertRybin

theorem orderThree_zero11_not_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (h00 : A 0 0 = 0) (hr : ∀ j, 0 < A 1 j ∧ 0 < A 2 j)
    (hc : ∀ i, 0 < A i 1 ∧ 0 < A i 2) : False := by
  have hsR (j : Fin 3) : 0 < A 1 j ↔ 0 < A 2 j := ⟨fun _ => (hr j).2, fun _ => (hr j).1⟩
  let B := blendThreeRows A 1 2 (1/2)
  obtain ⟨hB, hmB, hgB⟩ := orderThree_same_support_row_blend_globalMax hA hmass hmax 1 2
    (by decide) hsR (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have hpB (i j : Fin 3) : 0 < B i j ↔ 0 < A i j :=
    orderThree_half_row_blend_support hA 1 2 hsR i j
  have hsC (i : Fin 3) : 0 < B i 1 ↔ 0 < B i 2 :=
    ⟨fun _ => (hpB i 2).mpr (hc i).2, fun _ => (hpB i 1).mpr (hc i).1⟩
  let C := blendThreeColumns B 1 2 (1/2)
  obtain ⟨hC, hmC, hgC⟩ := orderThree_same_support_blend_globalMax hB hmB hgB 1 2
    (by decide) hsC (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have heq : C = orderThreeZeroBlock11 ((A 0 1+A 0 2)/2) ((A 1 0+A 2 0)/2)
      ((A 1 1+A 1 2+A 2 1+A 2 2)/4) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, B, blendThreeColumns, blendThreeRows, orderThreeZeroBlock11,
        Matrix.transpose_apply, h00] <;> ring
  change totalMass C = 3 at hmC
  change ∀ D : Board 3 3, (∀ i j, 0 ≤ D i j) → totalMass D = 3 →
    dittertFunctional D ≤ dittertFunctional C at hgC
  rw [heq] at hmC hgC
  exact orderThree_zero_block11_not_globalMax (div_pos (add_pos (hc 0).1 (hc 0).2) (by norm_num))
    (div_pos (add_pos (hr 0).1 (hr 0).2) (by norm_num))
    (div_pos (add_pos (add_pos (add_pos (hr 1).1 (hr 2).1) (hr 1).2) (hr 2).2) (by norm_num)) hmC hgC

theorem orderThree_zero12_not_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (h00 : A 0 0 = 0) (h01 : A 0 1 = 0) (ha : 0 < A 0 2)
    (hr : ∀ j, 0 < A 1 j ∧ 0 < A 2 j) : False := by
  have hsR (j : Fin 3) : 0 < A 1 j ↔ 0 < A 2 j := ⟨fun _ => (hr j).2, fun _ => (hr j).1⟩
  let B := blendThreeRows A 1 2 (1/2)
  obtain ⟨hB, hmB, hgB⟩ := orderThree_same_support_row_blend_globalMax hA hmass hmax 1 2
    (by decide) hsR (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have hpB (i j : Fin 3) : 0 < B i j ↔ 0 < A i j :=
    orderThree_half_row_blend_support hA 1 2 hsR i j
  have hsA (i : Fin 3) : 0 < A i 0 ↔ 0 < A i 1 := by
    fin_cases i
    · simp [h00, h01]
    · exact ⟨fun _ => (hr 1).1, fun _ => (hr 0).1⟩
    · exact ⟨fun _ => (hr 1).2, fun _ => (hr 0).2⟩
  have hsC (i : Fin 3) : 0 < B i 0 ↔ 0 < B i 1 := (hpB i 0).trans ((hsA i).trans (hpB i 1).symm)
  let C := blendThreeColumns B 0 1 (1/2)
  obtain ⟨hC, hmC, hgC⟩ := orderThree_same_support_blend_globalMax hB hmB hgB 0 1
    (by decide) hsC (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have heq : C = orderThreeZeroBlock12 (A 0 2) ((A 1 0+A 1 1+A 2 0+A 2 1)/4)
      ((A 1 2+A 2 2)/2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, B, blendThreeColumns, blendThreeRows, orderThreeZeroBlock12,
        Matrix.transpose_apply, h00, h01] <;> ring
  change totalMass C = 3 at hmC
  change ∀ D : Board 3 3, (∀ i j, 0 ≤ D i j) → totalMass D = 3 →
    dittertFunctional D ≤ dittertFunctional C at hgC
  rw [heq] at hmC hgC
  exact orderThree_zero_block12_not_globalMax ha
    (div_pos (add_pos (add_pos (add_pos (hr 0).1 (hr 1).1) (hr 0).2) (hr 1).2) (by norm_num))
    (div_pos (add_pos (hr 2).1 (hr 2).2) (by norm_num)) hmC hgC

theorem orderThree_zero22_not_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (h00 : A 0 0 = 0) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (h11 : A 1 1 = 0)
    (hc : ∀ i, 0 < A i 2) (hr : 0 < A 2 0 ∧ 0 < A 2 1) : False := by
  have hsR (j : Fin 3) : 0 < A 0 j ↔ 0 < A 1 j := by
    fin_cases j
    · simp [h00, h10]
    · simp [h01, h11]
    · exact ⟨fun _ => hc 1, fun _ => hc 0⟩
  let B := blendThreeRows A 0 1 (1/2)
  obtain ⟨hB, hmB, hgB⟩ := orderThree_same_support_row_blend_globalMax hA hmass hmax 0 1
    (by decide) hsR (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have hpB (i j : Fin 3) : 0 < B i j ↔ 0 < A i j :=
    orderThree_half_row_blend_support hA 0 1 hsR i j
  have hsA (i : Fin 3) : 0 < A i 0 ↔ 0 < A i 1 := by
    fin_cases i
    · simp [h00, h01]
    · simp [h10, h11]
    · exact ⟨fun _ => hr.2, fun _ => hr.1⟩
  have hsC (i : Fin 3) : 0 < B i 0 ↔ 0 < B i 1 := (hpB i 0).trans ((hsA i).trans (hpB i 1).symm)
  let C := blendThreeColumns B 0 1 (1/2)
  obtain ⟨hC, hmC, hgC⟩ := orderThree_same_support_blend_globalMax hB hmB hgB 0 1
    (by decide) hsC (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have heq : C = orderThreeZeroBlock22 ((A 0 2+A 1 2)/2) ((A 2 0+A 2 1)/2) (A 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, B, blendThreeColumns, blendThreeRows, orderThreeZeroBlock22,
        Matrix.transpose_apply, h00, h01, h10, h11] <;> ring
  change totalMass C = 3 at hmC
  change ∀ D : Board 3 3, (∀ i j, 0 ≤ D i j) → totalMass D = 3 →
    dittertFunctional D ≤ dittertFunctional C at hgC
  rw [heq] at hmC hgC
  exact orderThree_zero_block22_not_globalMax (by have := hc 0; have := hc 1; positivity)
    (div_pos (add_pos hr.1 hr.2) (by norm_num)) (hc 2) hmC hgC

theorem orderThree_singleton_opposite_not_globalMax {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
    (ha : 0 < A 0 0) (hc : 0 < A 0 2)
    (hr : ∀ i, i ≠ 0 → 0 < A i 1 ∧ 0 < A i 2) : False := by
  have hsR (j : Fin 3) : 0 < A 1 j ↔ 0 < A 2 j := by
    fin_cases j
    · simp [h10, h20]
    · exact ⟨fun _ => (hr 2 (by decide)).1, fun _ => (hr 1 (by decide)).1⟩
    · exact ⟨fun _ => (hr 2 (by decide)).2, fun _ => (hr 1 (by decide)).2⟩
  let B := blendThreeRows A 1 2 (1/2)
  obtain ⟨hB, hmB, hgB⟩ := orderThree_same_support_row_blend_globalMax hA hmass hmax 1 2
    (by decide) hsR (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
  have heq : B = orderThreeSingletonOppositeFull (A 0 0) ((A 1 1+A 2 1)/2)
      (A 0 2) ((A 1 2+A 2 2)/2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, blendThreeColumns, blendThreeRows, orderThreeSingletonOppositeFull,
        Matrix.transpose_apply, h01, h10, h20] <;> ring
  change totalMass B = 3 at hmB
  change ∀ D : Board 3 3, (∀ i j, 0 ≤ D i j) → totalMass D = 3 →
    dittertFunctional D ≤ dittertFunctional B at hgB
  rw [heq] at hmB hgB
  have hp1 := hr 1 (by decide)
  have hp2 := hr 2 (by decide)
  exact orderThree_singleton_opposite_full_not_globalMax ha
    (div_pos (add_pos hp1.1 hp2.1) (by norm_num)) hc
    (div_pos (add_pos hp1.2 hp2.2) (by norm_num)) hmB hgB

end DittertRybin
