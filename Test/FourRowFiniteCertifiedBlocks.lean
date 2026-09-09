import DR.Rectangular.FourRowFiniteCertifiedBlocks
import DR.Rectangular.FourRowFiniteBlockScaling

namespace DittertRybin
noncomputable section

example (s : Fin 10) {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 50) :
    (fourRowFiniteSeedTrivialMatrix s n
      (fourRowFinite5RoleValue (fourRowFiniteParameter 5 n))).PosDef := by
  have h := fourRowFinite5_trivial_posDef s _ (fourRowFiniteParameter_five hn)
  have hd : (5 : ℝ)/fourRowFiniteParameter 5 n = n := by
    exact fourRowFiniteParameter_dimension (a := 5) (n := n) (by decide) (by omega)
  rw [hd] at h
  exact h

example (s : Fin 10) {n : ℕ} (hn : 50 ≤ n ∧ n ≤ 500) :
    (fourRowFiniteSeedTrivialMatrix s n
      (fourRowFinite50RoleValue (fourRowFiniteParameter 50 n))).PosDef := by
  have h := fourRowFinite50_trivial_posDef s _ (fourRowFiniteParameter_fifty hn)
  have hd : (50 : ℝ)/fourRowFiniteParameter 50 n = n := by
    exact fourRowFiniteParameter_dimension (a := 50) (n := n) (by decide) (by omega)
  rw [hd] at h
  exact h

-- Division by the positive parameter gives the actual source role coefficients c=h/u.
example (s : Fin 10) (u : ℝ) (hu : 1/10 ≤ u ∧ u ≤ 1) :
    (fourRowFiniteSeedTrivialMatrix s (5/u)
      (fun key => fourRowFinite5RoleValue u key/u)).PosDef := by
  have he : (fun key => fourRowFinite5RoleValue u key/u) =
      (fun key => u⁻¹*fourRowFinite5RoleValue u key) := by
    funext key
    ring
  rw [he, fourRowFiniteSeedTrivialMatrix_smul]
  exact (fourRowFinite5_trivial_posDef s u hu).smul (inv_pos.mpr (by linarith : 0 < u))

example : (fourRowFiniteSeedRowMatrix 4 5 (fourRowFinite5RoleValue 1)).PosDef := by
  simpa using fourRowFinite5_row_posDef 4 1 (by norm_num) (by decide)

example : (fourRowFiniteSeedColumnMatrix 9 (fourRowFinite50RoleValue (1/10))).PosDef :=
  fourRowFinite50_column_posDef 9 (1/10) (by norm_num)

example : (fourRowFiniteSeedInteractionMatrix 6 (fourRowFinite50RoleValue 1)).PosDef :=
  fourRowFinite50_interaction_posDef 6 1 (by norm_num) (by decide)

example : ¬fourRowFiniteSeedRows 9 < 3 := by decide

#print axioms fourRowFiniteSeed_labels
#print axioms fourRowFinite5_trivial_posDef
#print axioms fourRowFinite50_trivial_posDef
#print axioms fourRowFinite5_row_posDef
#print axioms fourRowFinite50_row_posDef
#print axioms fourRowFinite5_column_posDef
#print axioms fourRowFinite50_column_posDef
#print axioms fourRowFinite5_interaction_posDef
#print axioms fourRowFinite50_interaction_posDef
#print axioms fourRowFiniteSeedTrivialMatrix_smul

end
end DittertRybin
