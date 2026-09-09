import DR.Rectangular.OrderThreeFourRowConcentration

namespace DittertRybin.Tests
open scoped BigOperators

-- The exact negative correction at the first retained dimension is preserved.
example : 1-separationProbability (uniformBoard 4 960) 3=1439/737280 := by
  rw [orderThreeFourRow_failure_uniform (by norm_num)]
  norm_num

-- The centered cubic is signed and includes the one-coordinate zero-variance boundary.
example : orderThreeFourRowColumnVariance (fun _ : Fin 1 => (-2:ℝ))=0 := by
  norm_num [orderThreeFourRowColumnVariance]
example {n : ℕ} (hn : 0<n) (a : Fin n → ℝ) :
    (∑ j,(3*a j^2-11*a j^3)) =
      3*(∑ j,a j)^2/n-11*(∑ j,a j)^3/(n:ℝ)^2+
        ∑ j,(a j-(∑ k,a k)/n)^2*(3-11*(a j+2*(∑ k,a k)/n)) :=
  orderThreeFourRow_centered_cubic hn a

-- Full probability matrices, with zeros allowed, supply both concentration inputs.
example {n : ℕ} (hn : 960≤n) {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3) :
    orderThreeFourRowColumnVariance (orderThreeFourRowColumnGauge P)*(n:ℝ)^2<5 ∧
      orderThreeFourRowVariance (rowSum P)*n<14 :=
  orderThreeFourRow_contender_variances hn hP hcont
example {n : ℕ} (hn : 960≤n) {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3) :
    (∀ j,colSum P j<7/(n:ℝ)) ∧ orderThreeFourRowVariance (rowSum P)<1/64 :=
  orderThreeFourRow_contender_concentration hn hP hcont

#print axioms orderThree_cellSquareSum_le_failure
#print axioms orderThreeFourRow_centered_cubic
#print axioms orderThreeFourRow_contender_variances
#print axioms orderThreeFourRow_contender_concentration
end DittertRybin.Tests
