import DR.Square.RefinedSweep
import Mathlib.Tactic.FinCases

/-!
Persistent checks for the exact path certificate and refined sweep interface.
The rational test vector below rejects a false Poincaré constant of nineteen.
-/

namespace DittertRybin.Tests.RefinedSweep

open scoped BigOperators
open Certificates

example : ∀ i, 0 < pathShiftPivots i := pathShiftPivots_pos

-- The checked centered matrix retains its constant-vector kernel.
example : ∀ i, (∑ j, pathShiftFourteen i j * (1 : ℚ)) = 0 := pathShiftFourteen_kernel

-- Corrupting the target principal block must fail the exact identity gate.
set_option maxRecDepth 100000 in
example : ¬ pathShiftCertificate.Valid
    (pathShiftFourteen.submatrix Fin.castSucc Fin.castSucc + 1) := by
  decide +kernel

example : (∑ _i : Fin 14, ((7 : ℝ) - (∑ _j : Fin 14, (7 : ℝ)) / 14) ^ 2) = 0 := by
  norm_num

example : (∑ _i : Fin 14, ((7 : ℝ) - (∑ _j : Fin 14, (7 : ℝ)) / 14) ^ 2) ≤
    20 * ∑ t : Fin 13, sweepGap (fun _ : Fin 14 => (7 : ℝ)) t ^ 2 :=
  path_poincare_fourteen (fun _ => 7)

private def nearExtremal : Fin 14 → ℝ := ![-100, -95, -85, -71, -53, -33, -11, 11, 33, 53, 71, 85, 95, 100]

-- These are exact rational arithmetic checks, independent of any numerical eigenvalue.
example : (∑ i, (nearExtremal i - (∑ j, nearExtremal j) / 14) ^ 2) = 70620 := by
  norm_num [nearExtremal, Fin.sum_univ_succ]

example : (∑ t : Fin 13, sweepGap nearExtremal t ^ 2) = 3542 := by
  norm_num [sweepGap, nearExtremal, Fin.sum_univ_succ]

example : ¬ (∑ i, (nearExtremal i - (∑ j, nearExtremal j) / 14) ^ 2) ≤
    19 * ∑ t : Fin 13, sweepGap nearExtremal t ^ 2 := by
  norm_num [sweepGap, nearExtremal, Fin.sum_univ_succ]

private noncomputable def uniformWeight : Fin 14 → ℝ := fun _ => 1 / 14
private def tiedScores : Fin 14 → ℝ := fun i => if i.val < 7 then 0 else 1

-- Seven repeated values on each side still have positive variance.
example : sweepVariance uniformWeight tiedScores = 1 / 4 := by
  norm_num [sweepVariance, sweepMean, uniformWeight, tiedScores, Fin.sum_univ_succ]

-- Disconnected conductances and zero energy do not invalidate the refined cut theorem.
example : ∃ S : Finset (Fin 14), S.Nonempty ∧ S ≠ Finset.univ ∧
    sweepMass uniformWeight S ≤ 1 / 2 ∧ sweepBoundary (fun _ _ => 0) S ≤ 0 := by
  have h := exists_refined_weighted_sweep_cut uniformWeight
    (by intro i; norm_num [uniformWeight]) (by norm_num [uniformWeight]) (1 / 14)
    (by intro i; rfl) (fun _ _ => 0) (by intro i j; rfl) (by intro i j; rfl)
    tiedScores (by norm_num [sweepVariance, sweepMean, uniformWeight, tiedScores, Fin.sum_univ_succ])
  simpa [sweepEnergy] using h

#print axioms DittertRybin.pathShiftCertificate_valid
#print axioms DittertRybin.path_poincare_fourteen
#print axioms DittertRybin.exists_refined_weighted_sweep_cut

end DittertRybin.Tests.RefinedSweep
