import DR.Rectangular.FourRowMinorantThreeExtrema

namespace DittertRybin.Test.FourRowMinorantThreeExtrema
open scoped BigOperators

example : threeMomentCurve ![1,2,3] 1 = ![2,3,1] := by
  funext i
  fin_cases i <;> norm_num [threeMomentCurve,threeMomentCoordinate,Matrix.cons_val_two]

example : threeMomentCurve ![1,2,3] (1/2) = ![9/7,22/7,11/7] := by
  funext i
  fin_cases i <;> norm_num [threeMomentCurve,threeMomentCoordinate,Matrix.cons_val_two]

example : HasDerivAt (fun x => ∏ i, threeMomentCurve ![1,2,3] x i) (-4) 0 := by
  convert! threeMomentCurve_product_hasDerivAt ![1,2,3] using 1
  norm_num [Matrix.cons_val_two]

-- The product is not preserved: replacing the derivative by zero is unsound.
example : ¬IsLocalExtr (fun x => ∏ i, threeMomentCurve ![1,2,3] x i) 0 := by
  intro h
  have hh := threeMomentCurve_product_extremum_repeated ![1,2,3] h
  norm_num [Matrix.cons_val_two] at hh

-- Signed input coordinates still preserve both moments exactly.
example (x : ℝ) : (∑ i, threeMomentCurve ![-1,2,3] x i)=4 := by
  rw [threeMomentCurve_sum]
  norm_num [Fin.sum_univ_succ]

-- Zero affine coefficient is covered without an assumed nonconstant objective.
example : ∃ r ∈ threeMomentFeasible 6 11 (fun _ => 1),
    (∀ u ∈ threeMomentFeasible 6 11 (fun _ => 1),
      (7 : ℝ)+0*(∏ i, r i) ≤ 7+0*(∏ i, u i)) ∧
    ((∃ i, r i=0) ∨ (∃ _i : Fin 3, (1 : ℝ)=0) ∨
      r 0=r 1 ∨ r 0=r 2 ∨ r 1=r 2) := by
  apply threeMomentFeasible_exists_affine_minimum 6 11 7 0 (fun _ => 1) continuous_const
  refine ⟨![1,2,3],?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [Matrix.cons_val_two]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Matrix.cons_val_two]
  · intro i; norm_num

#print axioms threeMomentCurve_sum
#print axioms threeMomentCurve_pair
#print axioms threeMomentCurve_product_hasDerivAt
#print axioms threeMomentCurve_eventually_feasible
#print axioms threeMomentFeasible_isCompact
#print axioms threeMomentFeasible_exists_affine_minimum

end DittertRybin.Test.FourRowMinorantThreeExtrema
