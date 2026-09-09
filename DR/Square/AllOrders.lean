import DR.Square.SpectralFive
import DR.Square.SpectralRange

/-!
# Dittert's unique maximum in every positive dimension

This release-target wrapper combines the proved orders one through five
with the complete spectral range. Its matrix domain is the full closed
nonnegative simplex of total mass n. The square probability corollary uses
the proved two-way normalization equivalence, retaining exact equality.
-/

namespace DittertRybin

/-- Dittert's inequality and unique equality case for every n ≥ 1. -/
theorem dittert_unique_maximum {n : ℕ} (hn : 0 < n) : DittertMaximizer n := by
  by_cases h6 : 6 ≤ n
  · exact dittert_ge_six h6
  · have hsmall : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl
    · exact dittert_order_one
    · exact dittert_order_two
    · exact dittert_order_three
    · exact dittert_order_four
    · exact dittert_order_five

/-- The full square endpoint of Rybin's probability formulation. -/
theorem uniform_maximum_square_endpoint {n : ℕ} (hn : 0 < n) : UniformMaximizer n n n :=
  (uniformMaximizer_iff_dittertMaximizer hn).mpr (dittert_unique_maximum hn)

end DittertRybin
