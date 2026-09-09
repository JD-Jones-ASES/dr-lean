import DR.Square.SpectralRange

/-! Scope expansion and exact crossing-mass controls for the completed spectral range. -/

open scoped BigOperators
open DittertRybin

/-- This is the original mass-n domain, with no support, stationarity or marginal premise. -/
example {n : ℕ} (hn : 6 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : (∑ i, ∑ j, A i j) = (n : ℝ)) :
    (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent ≤
      2 - (n.factorial : ℝ) / (n : ℝ) ^ n ∧
    ((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent =
      2 - (n.factorial : ℝ) / (n : ℝ) ^ n ↔ A = fun _ _ => (n : ℝ)⁻¹) := by
  exact dittert_ge_six hn A hA hmass

example : DittertMaximizer 7 := dittert_order_seven
example : DittertMaximizer 8 := dittert_ge_eight (by decide)
example : DittertMaximizer 100 := dittert_ge_seven (by decide)

example : UniformMaximizer 7 7 7 :=
  (uniformMaximizer_iff_dittertMaximizer (by decide)).mpr dittert_order_seven

private def testCrossBoard : Board 2 2 := !![1, 2; 3, 4]
private def testCrossSet : Finset (SquareVertices 2) :=
  ({0} : Finset (Fin 2)).disjSum {1}

/-- Both off-diagonal rectangles are counted once, with the normalization 2n. -/
example : sweepBoundary (squareConductance testCrossBoard) testCrossSet = 5 / 4 := by
  rw [squareSweepBoundary]
  norm_num [testCrossBoard, testCrossSet, cutMass,
    show ({1} : Finset (Fin 2))ᶜ = {0} by decide,
    show ({0} : Finset (Fin 2))ᶜ = {1} by decide]

example : sweepMass (squareVertexWeight testCrossBoard) testCrossSet = 9 / 4 := by
  rw [squareSweepMass]
  norm_num [testCrossBoard, testCrossSet,
    rowSum, colSum, Fin.sum_univ_two]

/-- Reject dropping the second crossing rectangle. -/
example : sweepBoundary (squareConductance testCrossBoard) testCrossSet ≠ 1 / 4 := by
  rw [squareSweepBoundary]
  norm_num [testCrossBoard, testCrossSet, cutMass,
    show ({1} : Finset (Fin 2))ᶜ = {0} by decide,
    show ({0} : Finset (Fin 2))ᶜ = {1} by decide]

#print axioms DittertRybin.dittert_ge_seven
#print axioms DittertRybin.dittert_ge_six
#print axioms DittertRybin.dittert_globalMax_cut_seven
#print axioms DittertRybin.spectral_cut_contradiction
