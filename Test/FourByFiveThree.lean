import DR.Rectangular.FourByFiveThree
import DR.ProbabilityScaling

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- Every one of the literal coefficient equations is checked independently of PSD.
example : FiniteK3CoefficientEquations (27/40)
    (fun k => (fourByFiveThreeCoefficient k:ℝ)) := fourByFiveThree_equations_real

-- Changing the first coefficient is rejected by an actual quartic equation.
example : (∑ k : Fin 93,(((finiteK3QuarticRows.get 0).get k:Nat):ℚ)*
      (fourByFiveThreeCoefficient k+(if k=0 then (1/200:ℚ) else 0)))≠
    (finiteK3QuarticMultiplicity.get 0:ℚ)*(27/40)-(finiteK3QuarticSuccesses.get 0:ℚ) := by
  decide +kernel

-- The semantic identity retains signed, unnormalized boards and its mass factor.
example (P : Board 4 5) :
    (27/40:ℝ)*totalMass P^4-totalMass P*separationProbability P 3=
      ∑ e : Fin 4 × Fin 5,∑ f : Fin 4 × Fin 5,
        unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
          quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
            (fun a => P a.1 a.2) := fourByFiveThree_homogeneous_identity P

private noncomputable def negativeUniform : Board 4 5 := fun _ _ => -1/10
private theorem negativeUniform_mass : totalMass negativeUniform=(-2:ℝ) := by
  norm_num [negativeUniform,totalMass,rowSum]
private theorem negativeUniform_value : separationProbability negativeUniform 3=(-27/5:ℝ) := by
  have h := separationProbability_smul (uniformBoard 4 5) 3 (-2)
  have hboard : (-2:ℝ) • uniformBoard 4 5=negativeUniform := by
    ext i j
    norm_num [uniformBoard,negativeUniform]
  rw [hboard,fourByFiveThree_uniform_value] at h
  norm_num at h ⊢
  exact h

-- At a negative uniform board the correct homogeneous gap vanishes.
example : (27/40:ℝ)*totalMass negativeUniform^4-
    totalMass negativeUniform*separationProbability negativeUniform 3=0 := by
  rw [negativeUniform_mass,negativeUniform_value]
  norm_num

-- Omitting S before F3 is detected on the same signed input.
example : (27/40:ℝ)*totalMass negativeUniform^4-
    separationProbability negativeUniform 3≠0 := by
  rw [negativeUniform_mass,negativeUniform_value]
  norm_num

-- Zero entries are permitted by the final theorem, with no KKT/support premise.
example {P : Board 4 5} (hP : IsProbability P) :
    (1/5:ℝ)*(∑ i,∑ j,(P i j-1/20)^2)≤27/40-separationProbability P 3 :=
  fourByFiveThree_stability hP

example : separationProbability (uniformBoard 4 5) 3=(27/40:ℝ) :=
  fourByFiveThree_uniform_value
example : UniformMaximizer 4 5 3 := uniformMaximizer_four_by_five_three
example : UniformMaximizer 5 4 3 := uniformMaximizer_five_by_four_three

#print axioms fourByFiveThree_equations_rational
#print axioms fourByFiveThree_homogeneous_identity
#print axioms fourByFiveThree_stability
#print axioms uniformMaximizer_four_by_five_three
#print axioms uniformMaximizer_five_by_four_three
end DittertRybin.Tests
