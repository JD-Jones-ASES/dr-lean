import DR.Square.FiveMinorTwoBlocks
import DR.Square.FiveMinorSingleton

/-! Actual sparse-boundary controls and kernel audits for the two minor branches. -/
namespace DittertRybin.Tests
open scoped BigOperators

private def firstTwo : Finset (Fin 5) := {0,1}

private theorem identity_crossing_zero (I : Finset (Fin 5)) :
    cutMass (1:Board 5 5) I Iᶜ = 0 := by
  unfold cutMass
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hne : i ≠ j := by
    intro heq
    subst j
    exact (Finset.mem_compl.mp hj) hi
  simp [hne]

-- A diagonal matrix has tied marginals and zero crossing, with all off-diagonal cells zero.
example :
    ((∏ i, rowSum (1:Board 5 5) i) * fiveSmallRowFactor 0 0 0 ≤
      ∏ i : firstTwo, ∑ j ∈ firstTwo, (1:Board 5 5) i j) ∧
    ((∏ j, colSum (1:Board 5 5) j) * fiveSmallColFactor 0 0 0 ≤
      ∏ j : firstTwo, ∑ i ∈ firstTwo, (1:Board 5 5) i j) ∧
    ((∏ i, rowSum (1:Board 5 5) i) * fiveLargeRowFactor 0 0 0 ≤
      ∏ i : ↥(firstTwoᶜ), ∑ j ∈ firstTwoᶜ, (1:Board 5 5) i j) ∧
    ((∏ j, colSum (1:Board 5 5) j) * fiveLargeColFactor 0 0 0 ≤
      ∏ j : ↥(firstTwoᶜ), ∑ i ∈ firstTwoᶜ, (1:Board 5 5) i j) := by
  apply five_two_block_actual_products
  · intro i j; simp only [Matrix.one_apply]; split <;> norm_num
  · simp [totalMass,rowSum,Matrix.one_apply]
  · norm_num [firstTwo]
  · norm_num [firstTwo]
  · constructor <;> intros <;> simp [rowSum,colSum,Matrix.one_apply]
  · intro i; norm_num [rowSum,Matrix.one_apply]
  · intro j; norm_num [colSum,Matrix.one_apply]
  · simp [rowSum,firstTwo,Matrix.one_apply]
  · simp [colSum,firstTwo,Matrix.one_apply]
  · rw [identity_crossing_zero]
    have h := identity_crossing_zero firstTwoᶜ
    simpa using h
  · norm_num

-- No crossing loss makes each of the four product factors exactly one.
example : fiveSmallRowFactor 0 0 0 = 1 ∧ fiveSmallColFactor 0 0 0 = 1 ∧
    fiveLargeRowFactor 0 0 0 = 1 ∧ fiveLargeColFactor 0 0 0 = 1 := by
  norm_num [fiveSmallRowFactor,fiveSmallColFactor,fiveLargeRowFactor,fiveLargeColFactor]

#print axioms cut_row_product_loss
#print axioms cut_col_product_lower_of_complement_upper
#print axioms five_two_block_actual_products
#print axioms five_singleton_actual_products
#print axioms five_two_block_actual_permanent_floors
#print axioms five_two_block_cut_contradiction
#print axioms five_singleton_actual_minor_floor
#print axioms five_singleton_actual_permanent_lower

end DittertRybin.Tests
