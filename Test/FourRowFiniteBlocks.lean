import DR.Rectangular.FourRowFiniteBlocks

namespace DittertRybin
noncomputable section

example : fourRowFiniteOrdinaryAverage 1 2
    (fun i j => if i = j then 3 else 7) 1 1 = 5 := by
  norm_num [fourRowFiniteOrdinaryAverage]

-- With one ordinary row, the distinct-row sector contributes nothing.
example : fourRowFiniteOrdinaryAverage 1 1
    (fun i j => if i = j then 3 else 700) 1 1 = 3 := by
  norm_num [fourRowFiniteOrdinaryAverage]

example : fourRowFiniteClearedColumnAverage 5 1 2
    (fun i j => if i = j then 3 else 7) 3 3 = 24/25 := by
  rw [← fourRowFiniteClearedColumnAverage_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num [fourRowFiniteOrdinaryAverage, fourRowFiniteDenominator, Fin.prod_univ_succ]

example : fourRowFiniteTrivialEntry 3 3 5 (fun _ => 17) [] (3,3) (3,3) = 17 := by
  norm_num [fourRowFiniteTrivialEntry, fourRowFiniteOrdinaryAverage,
    fourRowFiniteRealRoleEntry]

example (nr nc : ℕ) (n c : ℝ) (mark : List (ℕ × ℕ)) (j l : ℕ) :
    fourRowFiniteRowStandardEntry nr nc n (fun _ => c) mark j l = 0 := by
  simp [fourRowFiniteRowStandardEntry, fourRowFiniteOrdinaryAverage,
    fourRowFiniteRealRoleEntry]

example (nr nc : ℕ) (c : ℝ) (mark : List (ℕ × ℕ)) :
    fourRowFiniteInteractionEntry nr nc (fun _ => c) mark = 0 := by
  simp [fourRowFiniteInteractionEntry, fourRowFiniteRealRoleEntry]

-- Clearing an ordinary multiplicity really requires it to be nonzero.
example : ¬ (fourRowFiniteOrdinaryAverage 0 0 (fun _ _ => 1) 0 0 =
    ((1 : ℝ)/0)*1+(1-1/0)*1) := by
  norm_num [fourRowFiniteOrdinaryAverage]

#print axioms fourRowFiniteOrdinaryAverage_clear
#print axioms fourRowFiniteOrdinaryCount_parameter_pos
#print axioms fourRowFiniteTrivialEntry_clear
#print axioms fourRowFiniteRowStandardEntry_clear

end
end DittertRybin
