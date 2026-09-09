import DR.Rectangular.FourRowContenderConcentration
import DR.Rectangular.FourRowScalarGauge
import DR.Rectangular.FourRowRemainder

/-!
# Concentration with the actual scalar gap and collision remainder

The scalar gap and sampling remainder are now theorems. The column minorant
is the sole remaining input in this intermediate assembly; it is discharged
separately by the corrected four-row minorant proof.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates

theorem fourRow_actual_scalar_gap {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    29 / 32 + (61 / 512) * fourRowMarginalVariance (rowSum P) ≤
      (∑ i, rowSum P i * fourRowGaugeWeight (rowSum P) i) ^ 2 :=
  fourRowScalarGauge_gap (rowSum P) (rowSum_nonneg hP.1) hP.2

/-- Actual contender concentration with only the independently proved column minorant to supply. -/
theorem fourRow_contender_concentration_of_minorant {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) :
    fourRowMarginalVariance (rowSum P) * n < 10 ∧
      (∀ j, colSum P j < 7 / (2 * (n : ℝ))) ∧
      fourRowColumnSquareMass P < 7 / (5 * (n : ℝ)) :=
  fourRow_contender_concentration_of_leading hn P hP hcont hminor
    (fourRow_actual_scalar_gap P hP) (fourRow_failure_lower_of_leading P hP)

/-- Deletion and normalization use the actual board and require no extra concentration premise. -/
theorem fourRow_contender_deletion_of_minorant {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (a b : Fin n) (hab : a ≠ b) :
    493 / 500 ≤ totalMass (eraseColumns P {a,b}) ∧
      fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500 ∧
      fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
        totalMass (eraseColumns P {a,b})) ≤ 1 / 40 :=
  fourRow_contender_deletion_of_leading hn P hP hcont hminor
    (fourRow_actual_scalar_gap P hP) (fourRow_failure_lower_of_leading P hP) a b hab

end DittertRybin
