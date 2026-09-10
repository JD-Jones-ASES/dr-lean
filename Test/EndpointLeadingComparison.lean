import DR.Endpoint.LeadingContenderComparison
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The scalar product estimate includes its closed [0,1] boundary.
example : 1-(∑ i,(![0,1,1/2] : Fin 3 → ℝ) i)≤
    (Finset.univ : Finset (Fin 3)).prod (fun i => 1-(![0,1,1/2] : Fin 3 → ℝ) i) := by
  exact (endpoint_product_bonferroni Finset.univ _
    (by intro i _; fin_cases i <;> norm_num)
    (by intro i _; fin_cases i <;> norm_num)).1
example : 1-(∅ : Finset ℕ).sum (fun _ => (4:ℝ))≤
    (∅ : Finset ℕ).prod (fun _ => (1:ℝ)-4) := by
  exact (endpoint_product_bonferroni ∅ (fun _ : ℕ => (4:ℝ))
    (by simp) (by simp)).1
example : ¬(1-(∑ _i : Fin 3,(4:ℝ))≤
    (Finset.univ : Finset (Fin 3)).prod (fun _ => 1-(4:ℝ))) := by norm_num

-- The uniform correction vanishes at two draws but is strictly positive at three.
example : (Nat.choose 2 2:ℝ)/2-(1-distinctUniformProbability 2 2)=0 := by
  norm_num [distinctUniformProbability,Nat.descFactorial]
example : (Nat.choose 3 2:ℝ)/3-(1-distinctUniformProbability 3 3)=2/9 := by
  norm_num [distinctUniformProbability,Nat.descFactorial]
example : ¬(Nat.choose 3 2:ℝ)/3-(1-distinctUniformProbability 3 3)≤0 := by
  norm_num [distinctUniformProbability,Nat.descFactorial]
example : 0≤(Nat.choose 3 2:ℝ)/3-(1-distinctUniformProbability 3 3) ∧
    (Nat.choose 3 2:ℝ)/3-(1-distinctUniformProbability 3 3)≤
      (Nat.choose 3 2:ℝ)*(((3-2:ℕ):ℝ)*(((3-2:ℕ):ℝ)+3)/2)/(2*3^2) :=
  endpoint_uniform_collision_remainder (by decide) (by decide) (by decide)

-- A real uniform contender makes the full comparison non-vacuous.
example : (endpointLeadingGauge (uniformBoard 3 5))^2-(1-dittertConstant 3)+
      5*centeredVariance (endpointLeadingColumnCost (uniformBoard 3 5))≤
    5*(((3-2:ℕ):ℝ)*(((3-2:ℕ):ℝ)+3)/2)*(1/5)*marginalVariance (colSum (uniformBoard 3 5))+
      dittertConstant 3*(((3-2:ℕ):ℝ)*(((3-2:ℕ):ℝ)+3)/2)/(2*5) := by
  apply endpoint_contender_leading_comparison (by decide) (by decide)
    (uniformBoard 3 5) (uniformBoard_isProbability (by decide) (by decide))
    (le_of_eq (separationProbability_uniform (by decide) (by decide)).symm) (1/5)
  intro j
  norm_num [colSum,uniformBoard]

-- Balanced marginals alone do not give the contender comparison.
private noncomputable def diagonalBoard : Board 3 3 := fun i j => if i=j then 1/3 else 0
private theorem diagonalBoard_probability : IsProbability diagonalBoard := by
  constructor
  · intro i j
    unfold diagonalBoard
    split_ifs <;> norm_num
  · norm_num [totalMass,rowSum,diagonalBoard,Fin.sum_univ_succ]
private theorem diagonalBoard_cost : endpointLeadingColumnCost diagonalBoard=fun _ => 1/3 := by
  funext j
  unfold endpointLeadingColumnCost
  have hq : quadraticValue (endpointLeadingKernel (rowSum diagonalBoard))
      (fun i => diagonalBoard i j)=1/9 := by
    simp +contextual [quadraticValue,diagonalBoard,mul_ite,ite_mul,endpointLeadingKernel]
    norm_num
  rw [hq]
  norm_num
private theorem diagonalBoard_cols : colSum diagonalBoard=fun _ => 1/3 := by
  funext j
  fin_cases j <;> norm_num [colSum,diagonalBoard,Fin.sum_univ_succ]
example : ¬uniformSeparationValue 3 3 3≤separationProbability diagonalBoard 3 := by
  intro hcont
  have h := endpoint_contender_leading_comparison (by decide) (by decide) diagonalBoard
    diagonalBoard_probability hcont (1/3) (by intro j; rw [diagonalBoard_cols])
  norm_num [endpointLeadingGauge,diagonalBoard_cost,diagonalBoard_cols,centeredVariance,
    marginalVariance,dittertConstant,Nat.factorial] at h

#print axioms endpoint_product_bonferroni
#print axioms endpoint_uniform_collision_remainder
#print axioms endpoint_contender_leading_comparison

end DittertRybin.Tests
