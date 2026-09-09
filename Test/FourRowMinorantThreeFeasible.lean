import DR.Rectangular.FourRowMinorantThreeFeasible

namespace DittertRybin.Test.FourRowMinorantThreeFeasible
open scoped BigOperators

-- An actual non-repeated triple: the compact reduction is now discharged.
example : 0 ≤ fourRowMinorantHomogeneous ![3,2,1,1] (fourRowThreeStationary 3 2 1 1) := by
  apply fourRowThreeStationary_feasible_nonneg 3 2 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro i
  fin_cases i <;> norm_num [fourRowThreeStationary,fourRowThreePhi,fourRowThreeDenominator,
    Matrix.cons_val_two,Matrix.cons_val_three]

-- Closed feasibility, with one stationary coordinate exactly zero.
example : fourRowThreeStationary 3 1 1 5 = ![0,1/2,1/2,0] := by
  funext i
  fin_cases i <;> norm_num [fourRowThreeStationary,fourRowThreePhi,fourRowThreeDenominator,
    Matrix.cons_val_two,Matrix.cons_val_three]

example : 0 ≤ fourRowMinorantHomogeneous ![3,1,1,5] (fourRowThreeStationary 3 1 1 5) := by
  apply fourRowThreeStationary_feasible_nonneg 3 1 1 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro i
  fin_cases i <;> norm_num [fourRowThreeStationary,fourRowThreePhi,fourRowThreeDenominator,
    Matrix.cons_val_two,Matrix.cons_val_three]

-- Arbitrary real positive d and all closed feasible stationary coordinates.
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (hD : 0 < 4*(a*b+a*c+b*c)-(a+b+c)^2)
    (hfeas : ∀ i, 0 ≤ fourRowThreeStationary a b c d i) :
    0 ≤ fourRowMinorantHomogeneous ![a,b,c,d] (fourRowThreeStationary a b c d) :=
  fourRowThreeStationary_feasible_nonneg a b c d ha hb hc hd hD hfeas

#print axioms threeMomentFeasible_rows_pos
#print axioms fourRowThreeStationary_feasible_nonneg

end DittertRybin.Test.FourRowMinorantThreeFeasible
