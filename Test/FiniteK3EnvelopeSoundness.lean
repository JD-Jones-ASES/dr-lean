import DR.Certificates.FiniteK3EnvelopeSoundness
import DR.Certificates.FiniteK3Cases.M4N6

open DittertRybin DittertRybin.Certificates

-- All gates are literal checked data. No certificate validity is an assumption.
private theorem pilot : UniformMaximizer 4 6 3 :=
  FiniteK3Cases.C4N6.valid.uniformMaximizer (by decide)

private theorem pilot_value : uniformSeparationValue 4 6 3 = 13/18 := by
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

-- This includes sparse matrices: no cell, row, or column positivity is assumed.
example (P : Board 4 6) (hP : IsProbability P) :
    separationProbability P 3 ≤ 13/18 ∧
      (separationProbability P 3 = 13/18 ↔ P = uniformBoard 4 6) := by
  simpa only [pilot_value] using pilot P hP

-- The polynomial bridge remains signed and unnormalized even for this data.
example (P : Board 4 6) :
    (13/18) * totalMass P ^ 4 - totalMass P * separationProbability P 3 =
      ∑ e : Fin 4 × Fin 6, ∑ f : Fin 4 × Fin 6,
        unorderedPairWeight e f * P e.1 e.2 * P f.1 f.2 *
          quadraticValue (finiteK3Entry (fun i => (FiniteK3Cases.C4N6.coeff i : ℝ)) e f)
            (fun a => P a.1 a.2) := by
  have h := finiteK3_quartic_probability_identity
    FiniteK3Cases.C4N6.valid.coefficientEquations P
  simpa only [pilot_value] using h

#print axioms FiniteK3EnvelopeValid.coefficientEquations
#print axioms FiniteK3EnvelopeValid.representative
#print axioms FiniteK3EnvelopeValid.uniformMaximizer
#print axioms pilot
