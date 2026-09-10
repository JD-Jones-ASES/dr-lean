import DR.Endpoint.MarginalDiscrepancy
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- The centered-sign factor four is sharp on a genuine boundary probability vector.
example : (((![1,0] : Fin 2 → ℝ) 0)-1/2)^2 ≤
    (2 : ℝ)*marginalVariance (![1,0] : Fin 2 → ℝ)/4 := by
  simpa using probability_subset_sq_le_variance (by decide)
    (![1,0] : Fin 2 → ℝ) (by norm_num [Fin.sum_univ_succ]) {0}

example : ¬ (((1 : ℝ)-1/2)^2 ≤
    2*marginalVariance (![1,0] : Fin 2 → ℝ)/8) := by
  norm_num [marginalVariance, Fin.sum_univ_succ]

-- The variance estimate also holds for signed vectors of mass one.
example : (((2 : ℝ)-1/2)^2 ≤
    2*marginalVariance (![2,-1] : Fin 2 → ℝ)/4) := by
  simpa using probability_subset_sq_le_variance (by decide)
    (![2,-1] : Fin 2 → ℝ) (by norm_num [Fin.sum_univ_succ]) {0}

-- Mass normalization is necessary; the constant vector of mass two fails.
example : ¬ (((2 : ℝ)-1)^2 ≤
    2*marginalVariance (![1,1] : Fin 2 → ℝ)/4) := by
  norm_num [marginalVariance, Fin.sum_univ_succ]

-- The elementary bound retains epsilon=1/4 and a zero coordinate.
example : (((0 : ℝ)-1/3)^2 ≤ 2*(3-1)*(1/4)/(3*2)) := by
  have hs : (∑ i : Fin 3, (![1/2,1/2,0] : Fin 3 → ℝ) i) = 1 := by
    norm_num [Fin.sum_univ_succ]
  have he : 1-(1/4 : ℝ) ≤ normalizedElementarySuccess (![1/2,1/2,0] : Fin 3 → ℝ) 2 := by
    rw [normalizedElementarySuccess_two (by decide) hs]
    norm_num [marginalVariance, Fin.sum_univ_succ]
  simpa using elementary_subset_sq_le
    (x := (![1/2,1/2,0] : Fin 3 → ℝ)) (by intro i; fin_cases i <;> norm_num)
    hs (by decide) (by decide) (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num) he {2}

example : (1+2 : ℝ)^2 ≤ 1*(1+4)*2 :=
  shared_weighted_discrepancy_sq (by norm_num) (by norm_num)
    (r := 1) (s := 1) (by norm_num) (by norm_num) (by norm_num)

example : ¬ ((1+2 : ℝ)^2 ≤ 1*(1+1)*2) := by norm_num

example : dittertConstant 3 ≤ (1/4 : ℝ) := endpoint_a_le_quarter (by decide)
example : ¬ (dittertConstant 2 ≤ (1/4 : ℝ)) := by norm_num [dittertConstant, Nat.factorial]

-- Every subset, including the empty and full cuts, reaches the joint API.
example {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (P : Board m n)
    (hP : IsProbability P) (hc : uniformSeparationValue m n m ≤ separationProbability P m)
    (hb : distinctUniformProbability n m ≤ 1/4) (I : Finset (Fin m)) (J : Finset (Fin n)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)| +
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
      (2/(3*(m : ℝ)))*(1+((n : ℝ)-1)*dittertConstant m/distinctUniformProbability n m)*
        endpointRookDeficit P :=
  endpoint_contender_subset_discrepancy_sq hm hmn hP hc hb I J

#print axioms probability_subset_sq_le_variance
#print axioms endpoint_row_subset_sq
#print axioms elementary_subset_sq_le
#print axioms endpoint_a_le_quarter
#print axioms shared_weighted_discrepancy_sq
#print axioms endpoint_contender_subset_discrepancy_sq
end DittertRybin.Tests
