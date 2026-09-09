import DR.Rectangular.FourRowFiniteSeeds

/-! Exact scaling of the actual real block entries, for passing from h(u) to h(u)/u. -/

namespace DittertRybin
noncomputable section

theorem fourRowFiniteTrivialEntry_smul (nr nc : ℕ) (n d : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (x y : ℕ × ℕ) :
    fourRowFiniteTrivialEntry nr nc n (fun key => d*h key) mark x y =
      d*fourRowFiniteTrivialEntry nr nc n h mark x y := by
  simp only [fourRowFiniteTrivialEntry, fourRowFiniteRealRoleEntry,
    fourRowFiniteOrdinaryAverage_smul]

theorem fourRowFiniteRowStandardEntry_smul (nr nc : ℕ) (n d : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (i j : ℕ) :
    fourRowFiniteRowStandardEntry nr nc n (fun key => d*h key) mark i j =
      d*fourRowFiniteRowStandardEntry nr nc n h mark i j := by
  simp only [fourRowFiniteRowStandardEntry, fourRowFiniteRealRoleEntry, ← mul_sub,
    fourRowFiniteOrdinaryAverage_smul]

theorem fourRowFiniteColumnStandardEntry_smul (nr nc : ℕ) (d : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) (i j : ℕ) :
    fourRowFiniteColumnStandardEntry nr nc (fun key => d*h key) mark i j =
      d*fourRowFiniteColumnStandardEntry nr nc h mark i j := by
  simp only [fourRowFiniteColumnStandardEntry, fourRowFiniteRealRoleEntry, ← mul_sub,
    fourRowFiniteOrdinaryAverage_smul]

theorem fourRowFiniteInteractionEntry_smul (nr nc : ℕ) (d : ℝ) (h : ℕ → ℝ)
    (mark : List (ℕ × ℕ)) :
    fourRowFiniteInteractionEntry nr nc (fun key => d*h key) mark =
      d*fourRowFiniteInteractionEntry nr nc h mark := by
  simp only [fourRowFiniteInteractionEntry, fourRowFiniteRealRoleEntry]
  ring

theorem fourRowFiniteSeedTrivialMatrix_smul (s : Fin 10) (N d : ℝ) (h : ℕ → ℝ) :
    fourRowFiniteSeedTrivialMatrix s N (fun key => d*h key) =
      d • fourRowFiniteSeedTrivialMatrix s N h := by
  ext i j
  exact fourRowFiniteTrivialEntry_smul _ _ _ _ _ _ _ _

theorem fourRowFiniteSeedRowMatrix_smul (s : Fin 10) (N d : ℝ) (h : ℕ → ℝ) :
    fourRowFiniteSeedRowMatrix s N (fun key => d*h key) =
      d • fourRowFiniteSeedRowMatrix s N h := by
  ext i j
  exact fourRowFiniteRowStandardEntry_smul _ _ _ _ _ _ _ _

theorem fourRowFiniteSeedColumnMatrix_smul (s : Fin 10) (d : ℝ) (h : ℕ → ℝ) :
    fourRowFiniteSeedColumnMatrix s (fun key => d*h key) =
      d • fourRowFiniteSeedColumnMatrix s h := by
  ext i j
  exact fourRowFiniteColumnStandardEntry_smul _ _ _ _ _ _ _

theorem fourRowFiniteSeedInteractionMatrix_smul (s : Fin 10) (d : ℝ) (h : ℕ → ℝ) :
    fourRowFiniteSeedInteractionMatrix s (fun key => d*h key) =
      d • fourRowFiniteSeedInteractionMatrix s h := by
  ext i j
  exact fourRowFiniteInteractionEntry_smul _ _ _ _ _

end
end DittertRybin
