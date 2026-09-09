import DR.Square.SixMatrixBounds
import DR.Square.ScoreOrder

/-! Exact controls for the stationary singleton correction and score orientation. -/

namespace DittertRybin.Tests

open Certificates.SpectralSixGuards

-- The boundary u=0 is included, with no division by a vanishing marginal deficit.
example (v : ℝ) (hv : 0 ≤ v) : 0 - v ≤ 2 * (cellCorrection : ℝ) :=
  six_singleton_correction (by norm_num) hv (by nlinarith)

-- Deleting the stationarity constraint invalidates the singleton correction.
example : ¬ (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u - v ≤ 2 * (cellCorrection : ℝ)) := by
  intro h
  have hh := h 1 0 (by norm_num) (by norm_num)
  norm_num [cellCorrection] at hh

-- Positive row scores preserve order while the negated column score reverses it.
example : (2 : ℝ) * (1 / 2 - 1) / (1 / 2) < 2 * (3 / 2 - 1) / (3 / 2) := by norm_num
example : -(2 : ℝ) * (1 / 2 - 1) / (1 / 2) > -(2 : ℝ) * (3 / 2 - 1) / (3 / 2) := by norm_num

#print axioms six_globalMax_extremal_marginal_sum_either
#print axioms six_globalMax_singleton_cell_lower
#print axioms permanent_lower_bound_singleton_six
#print axioms singleton_lower_score_cut_extrema
#print axioms singleton_upper_score_cut_extrema

end DittertRybin.Tests
