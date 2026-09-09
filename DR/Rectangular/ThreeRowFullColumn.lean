import DR.Rectangular.ThreeRowNoSingleton
import DR.Rectangular.ThreeRowProperColumns

/-! Global three-row support reductions on every rectangle with at least three columns. -/

namespace DittertRybin

/-- Every actual three-row global maximizer has a fully positive physical column. -/
theorem IsSeparationGlobalMax.threeRow_exists_full_column {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n) :
    ∃ c, ThreeRowFullColumn P c := by
  by_contra hnone
  have hcols : ∀ c, ∃ i, ThreeRowDoublet P i c := by
    intro c
    rcases hmax.threeRow_columns_full_or_doublet hP hn c with hf | hd
    · exact False.elim (hnone ⟨c, hf⟩)
    · exact hd
  exact hmax.threeRow_not_doublet_only hP hn hcols

/-- Transposition retains an actual fully positive row in the three-column orientation. -/
theorem IsSeparationGlobalMax.threeColumn_exists_full_row {m : ℕ} {P : Board m 3}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hm : 3 ≤ m) :
    ∃ r, ∀ c, 0 < P r c := by
  obtain ⟨r, hr⟩ := hmax.transpose.threeRow_exists_full_column hP.transpose hm
  exact ⟨r, hr⟩

end DittertRybin
