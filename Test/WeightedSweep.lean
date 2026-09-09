import DR.Square.WeightedSweep
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Exact normalization and boundary controls for the finite weighted sweep theorem.
The two-vertex example attains the factor `(N - 1) / 4`; disconnected graphs,
score ties, and complementing a cut with excessive mass are retained.
-/

namespace DittertRybin.Tests.WeightedSweep

open scoped BigOperators

private noncomputable def half : Fin 2 → ℝ := fun _ => 1 / 2
private def binary : Fin 2 → ℝ := ![0, 1]
private def complete {N : ℕ} : Fin N → Fin N → ℝ := fun _ _ => 1

example : sweepVariance half binary = 1 / 4 := by
  norm_num [sweepVariance, sweepMean, half, binary, Fin.sum_univ_two]

-- The half-weighted ordered double sum counts the crossing edge once.
example : sweepEnergy complete binary = 1 := by
  norm_num [sweepEnergy, complete, binary, Fin.sum_univ_two]

example : sweepBoundary complete ({0} : Finset (Fin 2)) = 1 := by
  rw [sweepBoundary_eq_sum_ite]
  simp only [Fin.sum_univ_two]
  norm_num [complete]

-- The sharp two-vertex value rejects an erroneously improved factor 1/8.
example : ¬ sweepBoundary complete ({0} : Finset (Fin 2)) ≤
    sweepEnergy complete binary / (8 * sweepVariance half binary) := by
  rw [sweepBoundary_eq_sum_ite]
  simp only [Fin.sum_univ_two]
  norm_num [sweepEnergy, sweepVariance, sweepMean, complete, binary, half, Fin.sum_univ_two]

example : ∃ S : Finset (Fin 2), S.Nonempty ∧ S ≠ Finset.univ ∧
    sweepMass half S ≤ 1 / 2 ∧ sweepBoundary complete S ≤ 1 := by
  have h := exists_weighted_sweep_cut (by norm_num : 2 ≤ 2) half
    (by intro v; norm_num [half]) (by norm_num [half, Fin.sum_univ_two])
    complete (by intro v w; norm_num [complete]) (by intro v w; rfl)
    binary (by norm_num [sweepVariance, sweepMean, binary, half, Fin.sum_univ_two])
  norm_num [sweepEnergy, sweepVariance, sweepMean, complete, binary, half, Fin.sum_univ_two] at h
  exact h

-- A disconnected conductance law can have positive variance and exactly zero energy.
example : ∃ S : Finset (Fin 2), S.Nonempty ∧ S ≠ Finset.univ ∧
    sweepMass half S ≤ 1 / 2 ∧ sweepBoundary (fun _ _ => 0) S ≤ 0 := by
  have h := exists_weighted_sweep_cut (by norm_num : 2 ≤ 2) half
    (by intro v; norm_num [half]) (by norm_num [half, Fin.sum_univ_two])
    (fun _ _ => 0) (by intro v w; rfl) (by intro v w; rfl)
    binary (by norm_num [sweepVariance, sweepMean, binary, half, Fin.sum_univ_two])
  simpa [sweepEnergy] using h

private noncomputable def thirds : Fin 3 → ℝ := fun _ => 1 / 3
private def tied : Fin 3 → ℝ := ![0, 0, 1]

example : sweepGap tied 0 = 0 ∧ sweepGap tied 1 = 1 := by
  change (0 : ℝ) - 0 = 0 ∧ 1 - 0 = 1
  norm_num

example : ∃ S : Finset (Fin 3), S.Nonempty ∧ S ≠ Finset.univ ∧
    sweepMass thirds S ≤ 1 / 2 ∧ sweepBoundary complete S ≤ 9 / 2 := by
  have h := exists_weighted_sweep_cut (by norm_num : 2 ≤ 3) thirds
    (by intro v; norm_num [thirds]) (by norm_num [thirds, Fin.sum_univ_succ])
    complete (by intro v w; norm_num [complete]) (by intro v w; rfl)
    tied (by norm_num [sweepVariance, sweepMean, tied, thirds, Fin.sum_univ_succ])
  norm_num [sweepEnergy, sweepVariance, sweepMean, complete, tied, thirds, Fin.sum_univ_succ] at h
  exact h

-- Constant scores have zero variance, so the positive-variance division gate is essential.
example : ¬ 0 < sweepVariance half (fun _ => 7) := by
  norm_num [sweepVariance, sweepMean, half, Fin.sum_univ_two]

private noncomputable def skew : Fin 2 → ℝ := ![3 / 4, 1 / 4]

example : sweepMass skew ({0} : Finset (Fin 2)) > 1 / 2 ∧
    sweepMass skew ({1} : Finset (Fin 2)) ≤ 1 / 2 := by
  norm_num [sweepMass, skew]

example : ∃ S : Finset (Fin 2), S.Nonempty ∧ S ≠ Finset.univ ∧
    sweepMass skew S ≤ 1 / 2 ∧ sweepBoundary complete S ≤ 1 := by
  exact exists_balanced_sweep_cut skew (by norm_num [skew, Fin.sum_univ_two])
    complete (by intro v w; rfl) {0} (by simp)
    (by intro h; have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := h ▸ Finset.mem_univ _
        norm_num at this)
    1 (by rw [sweepBoundary_eq_sum_ite]; simp only [Fin.sum_univ_two]; norm_num [complete])

#print axioms DittertRybin.sweepVariance_le_range_sq
#print axioms DittertRybin.sweep_prefix_gap_energy_le
#print axioms DittertRybin.exists_weighted_sweep_cut

end DittertRybin.Tests.WeightedSweep
