import DR.Certificates.SpectralSix

/-!
# Exact negative controls for the order-six scalar improvements

At the rational parameter 3/20, retaining the old factor `1-t`, or discarding
the special singleton entry factor, destroys the required strict gap. These
controls concern the proof's scalar improvements, not counterexamples to P2.
-/

namespace DittertRybin.Certificates.SpectralSixTests
open SpectralSixGuards
noncomputable section

private def oldDenominator (t : ℝ) : ℝ := (2 / 15) * (1 - t) - energy t
private def oldCrossingBound (t : ℝ) : ℝ :=
  energy t * (2 * (1 - t) - energy t) / (2 * oldDenominator t)
private def oldSingletonGap (t : ℝ) : ℝ :=
  (1 - oldCrossingBound t / 2 - (cellCorrection : ℝ)) * (24 / 625) *
    (1 - t - oldCrossingBound t / 2) ^ 5 - ((5 / 324) - t ^ 2 / (6 + t ^ 2))
private def discardedCellGap (t : ℝ) : ℝ :=
  (24 / 625) * (sixDominationFactor t - crossingBound t / 2) ^ 6 -
    ((5 / 324) - t ^ 2 / (6 + t ^ 2))

theorem old_denominator_positive : 0 < oldDenominator (3 / 20) := by
  norm_num [oldDenominator, energy, height]

theorem old_factor_rejected : oldSingletonGap (3 / 20) < 0 := by
  norm_num [oldSingletonGap, oldCrossingBound, oldDenominator, energy, height, cellCorrection]

theorem discarded_cell_rejected : discardedCellGap (3 / 20) < 0 := by
  norm_num [discardedCellGap, crossingBound, crossingNumerator, denominator, energy, height,
    sixDominationFactor]

/-- The certified singleton improvement restores the strict gap at the same point. -/
theorem actual_singleton_gap_positive : 0 < SpectralSix.singletonGap (3 / 20) :=
  SpectralSix.singleton_gap_pos _ (by norm_num) (by norm_num)

theorem actual_nonsingleton_gap_positive : 0 < SpectralSix.nonsingletonGap (3 / 20) :=
  SpectralSix.nonsingleton_gap_pos _ (by norm_num) (by norm_num)

end
end DittertRybin.Certificates.SpectralSixTests
