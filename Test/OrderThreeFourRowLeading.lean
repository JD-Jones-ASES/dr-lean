import DR.Rectangular.OrderThreeFourRowLeading

namespace DittertRybin.Tests
open scoped BigOperators

-- Newton's identity includes a signed cubic column and its exact e3 correction.
example : 4*((1:ℝ)^3+(-1)^3+2^3+0^3)-6*(1-1+2+0)*(1^2+(-1)^2+2^2+0^2) =
    -2*(1-1+2+0)^3+12*orderThreeFourRowE3 ![1,-1,2,0] := by
  have h := orderThreeFourRow_column_cubic ![1,-1,2,0]
  norm_num [Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three] at h ⊢
  exact h

example {n : ℕ} (P : Board 4 n) (hmass : totalMass P=1) :
    orderThreeFailurePolynomial P = ∑ j,
      (3*orderThreeFourRowQuadratic (rowSum P) (fun i=>P i j)+4*(∑ i,P i j^3)-6*colSum P j*(∑ i,P i j^2)) :=
  orderThreeFailurePolynomial_four_columns P hmass

-- The actual event bridge is quantified over the entire closed simplex, with no column cap.
example {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    (∑ j,(3*orderThreeFourRowColumnGauge P j^2-11*orderThreeFourRowColumnGauge P j^3))≤
      1-separationProbability P 3 := orderThreeFourRow_failure_ge_gauge_cubic P hP

#print axioms orderThreeFailurePolynomial_four_columns
#print axioms orderThreeFourRowColumnGauge_cube
#print axioms orderThreeFourRow_failure_ge_gauge_cubic
end DittertRybin.Tests
