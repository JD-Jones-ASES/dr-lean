import DR.Endpoint.BoundaryRook
import DR.Square.OrderThree

namespace DittertRybin.Tests
open scoped BigOperators
open Matrix

private noncomputable def balancedTwoThree : Board 2 3 := !![0, 1/4, 1/4; 1/3, 1/12, 1/12]

private theorem balancedTwoThree_nonneg : ∀ i j, 0 ≤ balancedTwoThree i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [balancedTwoThree]
private theorem balancedTwoThree_rows : ∀ i, rowSum balancedTwoThree i = 1/(2 : ℝ) := by
  intro i
  fin_cases i <;> norm_num [balancedTwoThree, rowSum, Fin.sum_univ_succ]
private theorem balancedTwoThree_columns : ∀ j, colSum balancedTwoThree j = 1/(3 : ℝ) := by
  intro j
  fin_cases j <;> norm_num [balancedTwoThree, colSum, Fin.sum_univ_succ]

-- A nonsquare balanced board with an actual zero receives the exact b*kappa floor.
example : (3/4 : ℝ) ≤ endpointRookRatio balancedTwoThree := by
  have h := endpointRookRatio_boundary_lower_bound (by decide) (by decide) (by decide)
    balancedTwoThree_nonneg balancedTwoThree_rows balancedTwoThree_columns ⟨0,0,rfl⟩
  norm_num [distinctUniformProbability, boundaryPermanentRatio, boundaryPermanentFloor,
    dittertConstant, Nat.descFactorial, Nat.factorial] at h ⊢
  exact h

-- Positive scaling can recover the zero from the dominating board itself.
example : (3/4 : ℝ) ≤ endpointRookRatio balancedTwoThree := by
  have h := endpointRookRatio_boundary_lower_bound_of_boundary_domination
    (t := 0) (P := balancedTwoThree) (by decide) (by decide) (by decide)
    balancedTwoThree_nonneg balancedTwoThree_rows balancedTwoThree_columns
    ⟨0,0,rfl⟩ (by norm_num) (fun _ _ => by simp)
  norm_num [distinctUniformProbability, boundaryPermanentRatio, boundaryPermanentFloor,
    dittertConstant, Nat.descFactorial, Nat.factorial] at h ⊢
  exact h

-- The exponent is the number of original rows, not the padded square dimension.
example : (3/16 : ℝ) ≤ endpointRookRatio ((1/2 : ℝ) • balancedTwoThree) := by
  have h := endpointRookRatio_boundary_lower_bound_of_smul_le
    (P := (1/2 : ℝ) • balancedTwoThree) (c := 1/2)
    (by decide) (by decide) (by decide) balancedTwoThree_nonneg
    balancedTwoThree_rows balancedTwoThree_columns ⟨0,0,rfl⟩ (by norm_num)
    (fun _ _ => le_rfl)
  norm_num [distinctUniformProbability, boundaryPermanentRatio, boundaryPermanentFloor,
    dittertConstant, Nat.descFactorial, Nat.factorial] at h ⊢
  exact h

-- The zero scaling endpoint is included without division by 1-t.
example : 0 ≤ endpointRookRatio (0 : Board 2 3) := by
  have h := endpointRookRatio_boundary_lower_bound_of_scaled_le
    (P := 0) (t := 1) (by decide) (by decide) (by decide)
    balancedTwoThree_nonneg balancedTwoThree_rows balancedTwoThree_columns
    ⟨0,0,rfl⟩ (by norm_num) (fun _ _ => by simp)
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul] using h

example (B : Board 3 5) : endpointRookRatio ((-2 : ℝ) • B) = -8 * endpointRookRatio B := by
  rw [endpointRookRatio_smul]
  norm_num

-- Exact cancellation covers the no-dummy-row and no-original-row cases.
example (B : Board 3 3) : (rectangularPadding (le_refl 3) B).permanent = endpointRookRatio B := by
  simpa using permanent_rectangularPadding_eq_endpointRookRatio (le_refl 3) B
example : ((5 : ℕ).factorial : ℝ)/(5 : ℝ)^5 * distinctUniformProbability 5 0 =
    dittertConstant 5 := by
  simpa using rectangularPadding_factor_mul_uniform (by decide : 0 ≤ 5)

private noncomputable def sharpThreeProbability : Board 3 3 :=
  fun i j => if i = 0 then (if j = 0 then 0 else 1/6)
    else if j = 0 then 1/6 else 1/12

-- The n=3 square lower constant remains sharp in probability normalization.
example : endpointRookRatio sharpThreeProbability =
    distinctUniformProbability 3 3 * boundaryPermanentRatio 3 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rw [endpointRookRatio, rookSum_endpoint_eq_rowAvoidance, rowAvoidance_square_eq_permanent,
    permanent_three]
  norm_num [sharpThreeProbability, h20, distinctUniformProbability, boundaryPermanentRatio,
    boundaryPermanentFloor, dittertConstant, Nat.descFactorial, Nat.factorial]

-- Raising the square floor from 1/4 to 1/3 fails at that actual zero board.
example : ¬(1/3 : ℝ) ≤ endpointRookRatio sharpThreeProbability := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rw [endpointRookRatio, rookSum_endpoint_eq_rowAvoidance, rowAvoidance_square_eq_permanent,
    permanent_three]
  norm_num [sharpThreeProbability, h20]

-- Without nonzero scaling, a zero in P does not imply a zero in B.
example : (∀ i j, (0 : ℝ) * uniformBoard 2 3 i j ≤ (0 : Board 2 3) i j) ∧
    ¬∃ i j, uniformBoard 2 3 i j = 0 := by
  constructor
  · intro i j
    simp
  · norm_num [uniformBoard]

#print axioms endpointRookRatio_mono
#print axioms endpointRookRatio_smul
#print axioms rectangularPadding_factor_mul_uniform
#print axioms permanent_rectangularPadding_eq_endpointRookRatio
#print axioms endpointRookRatio_boundary_lower_bound
#print axioms endpointRookRatio_boundary_lower_bound_of_smul_le
#print axioms endpointRookRatio_boundary_lower_bound_of_scaled_le
#print axioms endpointRookRatio_boundary_lower_bound_of_boundary_domination

end DittertRybin.Tests
