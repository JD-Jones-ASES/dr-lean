import DR.Rectangular.FourByFourThree

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- All seventeen source representatives, in the literal factor-64 convention.
example : fourByFourThreeSeedCode 0 0=39 ∧ fourByFourThreeSeedCode 0 1=(-2) ∧
    fourByFourThreeSeedCode 0 4=(-2) ∧ fourByFourThreeSeedCode 0 5=(-3) ∧
    fourByFourThreeSeedCode 1 1=121 ∧ fourByFourThreeSeedCode 1 2=(-25) ∧
    fourByFourThreeSeedCode 1 4=21 ∧ fourByFourThreeSeedCode 1 5=48 ∧
    fourByFourThreeSeedCode 1 6=(-46) ∧ fourByFourThreeSeedCode 4 4=121 ∧
    fourByFourThreeSeedCode 4 5=48 ∧ fourByFourThreeSeedCode 4 8=(-25) ∧
    fourByFourThreeSeedCode 4 9=(-46) ∧ fourByFourThreeSeedCode 5 5=123 ∧
    fourByFourThreeSeedCode 5 6=17 ∧ fourByFourThreeSeedCode 5 9=17 ∧
    fourByFourThreeSeedCode 5 10=(-25) := by decide +kernel

-- A single changed diagonal entry is rejected by the constant-kernel check.
example : (∑ j : Fin 16,(fourByFourThreeSeed 0 j+(if j=0 then (1/64:ℚ) else 0)))≠0 := by
  rw [Finset.sum_add_distrib,fourByFourThreeMatrix_checks.2.2 0]
  norm_num

-- Adding the centering projection preserves the constant kernel but destroys the cubic gate.
example : (∑ j,centeringMatrix 16 (0:Fin 16) j)=0 := by
  norm_num [centeringMatrix,Fin.sum_univ_succ]
example : 3*(fourByFourThreeMatrix 0 0 0+centeringMatrix 16 0 0)≠
    3*((39/64:ℚ)-if fourByFourThreeSuccess 0 0 0 then 1 else 0) := by
  decide +kernel

-- Signed unnormalized inputs are retained by the exact identity.
example (P : Board 4 4) : (39/64:ℝ)*totalMass P^3-separationProbability P 3=
    ∑ e,fourByFourThreeFlat P e*quadraticValue
      ((fourByFourThreeMatrix e).map (fun q : ℚ => (q:ℝ))) (fourByFourThreeFlat P) :=
  fourByFourThree_homogeneous_identity P

private def singleCell (t : ℝ) : Board 4 4 :=
  fun i j => if i.val=0 ∧ j.val=0 then t else 0

-- Negative mass is neither silently normalized nor removed from the polynomial theorem.
example : totalMass (singleCell (-2))=(-2:ℝ) ∧ separationProbability (singleCell (-2)) 3=0 := by
  rw [separationProbability_three_homogeneous]
  simp only [singleCell,totalMass,rowSum,colSum,orderThreeFailurePolynomial,Fin.sum_univ_four]
  norm_num [Fin.ext_iff]

-- A one-cell boundary distribution has the asserted literal Frobenius distance.
example : IsProbability (singleCell 1) ∧ fourByFourThreeEnergy (singleCell 1)=15/16 := by
  constructor
  · constructor
    · intro i j
      simp only [singleCell]
      split_ifs <;> norm_num
    · simp only [totalMass,rowSum,singleCell,Fin.sum_univ_four]
      norm_num [Fin.ext_iff]
  · simp only [fourByFourThreeEnergy,singleCell,Fin.sum_univ_four]
    norm_num [Fin.ext_iff]

example : separationProbability (uniformBoard 4 4) 3=(39/64:ℝ) := by
  rw [separationProbability_uniform (by norm_num) (by norm_num)]
  norm_num [uniformSeparationValue,distinctUniformProbability]

-- Full closed-simplex stability and uniqueness, with no KKT or support premise.
example {P : Board 4 4} (hP : IsProbability P) :
    (1/20:ℝ)*(∑ i,∑ j,(P i j-1/16)^2)≤39/64-separationProbability P 3 :=
  fourByFourThree_stability hP
example : UniformMaximizer 4 4 3 := uniformMaximizer_four_by_four_three

#print axioms fourByFourThreeGram_valid
#print axioms fourByFourThree_triple_identity
#print axioms fourByFourThreeMatrix_lower
#print axioms separationProbability_fourByFourThree_flat
#print axioms fourByFourThree_homogeneous_identity
#print axioms fourByFourThree_stability
#print axioms uniformMaximizer_four_by_four_three
end DittertRybin.Tests
