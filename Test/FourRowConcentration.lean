import DR.Rectangular.FourRowContenderConcentration

/-! Actual contender input, boundary gauges, and the precise remaining leading interface. -/

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

example {n : ℕ} (hn : 500 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (j : Fin n) : colSum P j < 21 / 100 :=
  fourRow_contender_initial_colSum hn hP hcont j

example : 1 - separationProbability (uniformBoard 4 500) 4 =
    (29 / 32 : ℝ) * (6 / 500 - 11 / 500^2 + 6 / 500^3) :=
  fourRow_failure_uniform (by decide)

private theorem boundary_gauge_collision :
    fourRowGaugeCollision ![0,1/2,1/2,0] 0 = 1 / 4 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  norm_num [fourRowGaugeCollision, hu, Finset.sum_insert, Finset.erase_insert,
    Finset.erase_insert_of_ne, Finset.erase_singleton, Fin.ext_iff]
  have h2 : (![0,1/2,1/2,0] : Fin 4 → ℝ) 2 = 1/2 := rfl
  have h3 : (![0,1/2,1/2,0] : Fin 4 → ℝ) 3 = 0 := rfl
  rw [h2, h3]
  norm_num

example : ¬ (fourRowGaugeCollision ![0,1/2,1/2,0] 0 ≤ 3 / 32) := by
  rw [boundary_gauge_collision]
  norm_num

example : fourRowGaugeWeight ![0,1/2,1/2,0] 0 = Real.sqrt (3 / 4) := by
  rw [fourRowGaugeWeight, boundary_gauge_collision]
  norm_num

/-- The exact centered cubic identity includes signed coordinates and has no concentration premise. -/
example : (∑ j : Fin 2, (6 * ![1,-3] j ^ 2 - 17 * ![1,-3] j ^ 3) : ℝ) =
    6 * (∑ j : Fin 2, ![1,-3] j) ^ 2 / 2 - 17 * (∑ j : Fin 2, ![1,-3] j) ^ 3 / 2^2 +
      ∑ j : Fin 2, (![1,-3] j - (∑ k : Fin 2, ![1,-3] k) / 2) ^ 2 *
        (6 - 17 * (![1,-3] j + 2 * (∑ k : Fin 2, ![1,-3] k) / 2)) :=
  fourRow_centered_cubic (by decide) ![1,-3]

/-- All kernel hypotheses are conclusions; only the three independent leading obligations remain. -/
example {n : ℕ} (hn : 500 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (hgap : 29 / 32 + (61 / 512) * fourRowMarginalVariance (rowSum P) ≤
      (∑ i, rowSum P i * fourRowGaugeWeight (rowSum P) i) ^ 2)
    (hremainder : 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
      11 * (∑ j, colSum P j ^ 3) ≤ 1 - separationProbability P 4)
    (a b : Fin n) (hab : a ≠ b) (hdiff : ∃ i, P i a ≠ P i b) :
    separationProbability P 4 < separationProbability (blendColumns P a b (1/2)) 4 := by
  obtain ⟨hm, hα, hν⟩ := fourRow_contender_deletion_of_leading hn P hP hcont hminor hgap hremainder a b hab
  exact fourRow_separationProbability_blend_strict P hP.1 a b hab (1/2)
    (by norm_num) (by norm_num) hdiff hm hα hν

#print axioms DittertRybin.fourRow_contender_initial_colSum
#print axioms DittertRybin.fourRowGaugeCollision_bounds
#print axioms DittertRybin.fourRowGaugeColumn_cube
#print axioms DittertRybin.fourRow_gauge_variance_bounds
#print axioms DittertRybin.fourRow_gauge_column_bounds
#print axioms DittertRybin.fourRow_pair_deletion_mass_variance
#print axioms DittertRybin.fourRow_contender_deletion_of_leading
