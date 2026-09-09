import DR.Rectangular.FourRowGauge
import DR.Rectangular.FourRowDeletionBounds

/-!
# Concentration assembly from the independent leading estimates

The three leading inputs below are explicit upstream proof obligations:
the corrected minorant, the scalar gauge gap, and the actual collision
remainder. All concentration and pair-deletion conclusions are derived.
This module does not claim those upstream obligations have been discharged.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates

/-- The proved cubic gauge comparison converts the actual remainder to the scalar bootstrap. -/
theorem fourRow_failure_ge_gauge_cubic {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (hremainder : 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
      11 * (∑ j, colSum P j ^ 3) ≤ 1 - separationProbability P 4) :
    (∑ j, (6 * fourRowGaugeColumn P j ^ 2 - 17 * fourRowGaugeColumn P j ^ 3)) ≤
      1 - separationProbability P 4 := by
  have hM := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hminor j)
  have hC : 11 * (∑ j, colSum P j ^ 3) ≤ 17 * (∑ j, fourRowGaugeColumn P j ^ 3) := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => fourRowGaugeColumn_cube P hP j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-- Every concentration conclusion follows from the actual contender and the independent leading inputs. -/
theorem fourRow_contender_concentration_of_leading {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (hgap : 29 / 32 + (61 / 512) * fourRowMarginalVariance (rowSum P) ≤
      (∑ i, rowSum P i * fourRowGaugeWeight (rowSum P) i) ^ 2)
    (hremainder : 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
      11 * (∑ j, colSum P j ^ 3) ≤ 1 - separationProbability P 4) :
    fourRowMarginalVariance (rowSum P) * n < 10 ∧
      (∀ j, colSum P j < 7 / (2 * (n : ℝ))) ∧
      fourRowColumnSquareMass P < 7 / (5 * (n : ℝ)) := by
  have ha0 (j : Fin n) : 0 ≤ fourRowGaugeColumn P j := (fourRowGaugeColumn_bounds P hP j).1
  have ha (j : Fin n) : fourRowGaugeColumn P j ≤ 21 / 100 :=
    ((fourRowGaugeColumn_bounds P hP j).2.1.trans_lt
      (fourRow_contender_initial_colSum hn hP hcont j)).le
  have hH := fourRowGaugeColumn_sum_le_one P hP
  have hupper : 1 - separationProbability P 4 ≤
      (29 / 32 : ℝ) * (6 / n - 11 / (n : ℝ) ^ 2 + 6 / (n : ℝ) ^ 3) := by
    rw [← fourRow_failure_uniform (by omega)]
    exact sub_le_sub_left hcont 1
  rw [← fourRowGaugeColumn_sum P] at hgap
  obtain ⟨hV, hrow⟩ := fourRow_gauge_variance_bounds hn (fourRowGaugeColumn P) ha0 ha hH
    (fourRowMarginalVariance (rowSum P)) (1 - separationProbability P 4)
    (fourRowMarginalVariance_nonneg _) hgap (fourRow_failure_ge_gauge_cubic P hP hminor hremainder) hupper
  obtain ⟨hcol, hsecond⟩ := fourRow_gauge_column_bounds hn (fourRowGaugeColumn P) (colSum P)
    ha0 hH hV (fun j => (fourRowGaugeColumn_bounds P hP j).2.2)
  exact ⟨hrow, hcol, hsecond⟩

/-- Pair deletion and row normalization add no further assumptions to the concentration assembly. -/
theorem fourRow_contender_deletion_of_leading {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (hgap : 29 / 32 + (61 / 512) * fourRowMarginalVariance (rowSum P) ≤
      (∑ i, rowSum P i * fourRowGaugeWeight (rowSum P) i) ^ 2)
    (hremainder : 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
      11 * (∑ j, colSum P j ^ 3) ≤ 1 - separationProbability P 4)
    (a b : Fin n) (hab : a ≠ b) :
    493 / 500 ≤ totalMass (eraseColumns P {a,b}) ∧
      fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500 ∧
      fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
        totalMass (eraseColumns P {a,b})) ≤ 1 / 40 := by
  obtain ⟨hrow, hcol, hsecond⟩ := fourRow_contender_concentration_of_leading hn P hP
    hcont hminor hgap hremainder
  exact fourRow_pair_deletion_bounds hn P hP hrow hcol hsecond a b hab

end DittertRybin
