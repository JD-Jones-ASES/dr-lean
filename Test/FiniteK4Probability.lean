import DR.Certificates.FiniteK4FixedSeedProbability
import DR.Rectangular.FourRowFiniteProbability

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

-- Both closed interval endpoints use the sharp physical probability, rather
-- than treating the polynomial parameter as an independent board dimension.
example : fourRowFiniteParameter 5 5 = 1 := by norm_num [fourRowFiniteParameter]
example : fourRowFiniteParameter 5 50 = 1/10 := by norm_num [fourRowFiniteParameter]
example : fourRowFiniteParameter 50 500 = 1/10 := by norm_num [fourRowFiniteParameter]

-- The coefficient equations alone extend outside the PSD interval. Keeping
-- this case prevents accidentally conflating the two distinct obligations.
example : FiniteK4FourRowCoefficientEquations (uniformSeparationValue 4 4 4)
    (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator50 (fourRowFiniteParameter 50 4)) :=
  fourRowFinite50_coefficientEquations (by decide)

-- Homogeneity retains signed boards of zero total mass; no normalization or
-- division by that mass is used, even on a nonzero signed board.
example {m n : ℕ} (P : Board m n) (hP : totalMass P = 0) :
    (∑ t : Fin 3 → Fin m × Fin n, unorderedTripleWeight t*(∏ i, P (t i).1 (t i).2)*
      quadraticValue (finiteK4Entry (fun k => (finiteK4Fixed5Coefficient k : ℝ)) t)
        (fun e => P e.1 e.2)) = 0 := by
  have h := finiteK4Fixed5_equations.probability_identity P
  simpa only [hP, zero_pow (by decide : 5 ≠ 0), mul_zero, zero_mul, sub_self] using h.symm

-- The fixed seed equations apply to the actual board and actual sharp target;
-- nonnegativity is unnecessary for this polynomial identity.
example (P : Board 20 20) :
    uniformSeparationValue 20 20 4*totalMass P^5-totalMass P*separationProbability P 4 =
      ∑ t : Fin 3 → Fin 20 × Fin 20, unorderedTripleWeight t*(∏ i, P (t i).1 (t i).2)*
        quadraticValue (finiteK4Entry (fun k => (finiteK4Fixed20Coefficient k : ℝ)) t)
          (fun e => P e.1 e.2) :=
  finiteK4Fixed20_sharp_equations.probability_identity P

example : uniformSeparationValue 5 5 4 ≠ 5425/15625 := by
  rw [finiteK4Fixed5_uniform_value]
  norm_num

#print axioms FiniteK4CoefficientEquations.local
#print axioms FiniteK4CoefficientEquations.probability_identity
#print axioms FiniteK4CoefficientEquations.uniformMaximizer
#print axioms fourRowFiniteParameter_uniform_value
#print axioms fourRowFinite5_coefficientEquations
#print axioms fourRowFinite50_coefficientEquations
#print axioms FiniteK4FourRowCoefficientEquations.uniformMaximizer
#print axioms finiteK4Fixed5_sharp_equations
#print axioms finiteK4Fixed20_sharp_equations
end DittertRybin.Tests
