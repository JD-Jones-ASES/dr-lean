import DR.Endpoint.BoundaryPermanentRatio
import DR.Square.OrderThree

namespace DittertRybin.Tests
open scoped BigOperators
open Matrix

private noncomputable def boundaryThree : Board 3 3 :=
  fun i j => if i = 0 then (if j = 0 then 0 else 1/2)
    else if j = 0 then 1/2 else 1/4

private theorem boundaryThree_ds : boundaryThree ∈ doublyStochastic ℝ (Fin 3) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [boundaryThree]
  · intro i
    fin_cases i <;> norm_num [boundaryThree,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [boundaryThree,Fin.sum_univ_succ]

-- The included n=3 boundary is sharp at an actual doubly stochastic matrix.
example : boundaryPermanentFloor 3 ≤ boundaryThree.permanent :=
  permanent_boundary_lower_bound (by decide) boundaryThree_ds ⟨0,0,by rfl⟩

example : boundaryThree.permanent = boundaryPermanentFloor 3 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rw [permanent_three]
  norm_num [boundaryThree,boundaryPermanentFloor,h20]

example : ¬ (1/3 : ℝ) ≤ boundaryThree.permanent := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rw [permanent_three]
  norm_num [boundaryThree,h20]

example : boundaryPermanentFloor 3 = (1/4 : ℝ) ∧ boundaryPermanentFloor 4 = (8/81 : ℝ) := by
  norm_num [boundaryPermanentFloor,Nat.factorial]

example : boundaryPermanentRatio 3 = (9/8 : ℝ) := by
  norm_num [boundaryPermanentRatio,boundaryPermanentFloor,dittertConstant,Nat.factorial]

-- The arbitrary zero is not required to be at the first row or column.
example {n : ℕ} (hn : 3 ≤ n) (A : Board n n)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (i j : Fin n) (hz : A i j = 0) :
    boundaryPermanentFloor n ≤ A.permanent :=
  permanent_boundary_lower_bound hn hA ⟨i,j,hz⟩

example : (16/17 : ℝ)^2/(3*(18-1)^2) <
    (boundaryPermanentRatio 18-1)/(boundaryPermanentRatio 18)^2 :=
  boundaryPermanentRatio_gap (by decide)

example : (16/17 : ℝ)^2/(3*(1000-1)^2) <
    (boundaryPermanentRatio 1000-1)/(boundaryPermanentRatio 1000)^2 :=
  boundaryPermanentRatio_gap (by decide)

-- The stronger unsupported coefficient one is rejected by exact n=18 arithmetic.
example : ¬ 1/(17 : ℝ)^2 < boundaryPermanentRatio 18-1 := by
  norm_num [boundaryPermanentRatio,boundaryPermanentFloor,dittertConstant,Nat.factorial]

example : 1-(4 : ℝ)*0+4*(4-1)/2*0^2-4*(4-1)*(4-2)/6*0^3 ≤ (1-0)^4 :=
  boundary_bernoulli_cubic_lower (by decide) (by norm_num) (by norm_num)

example : 1-(2 : ℝ)*1+2*(2-1)/2*1^2-2*(2-1)*(2-2)/6*1^3 ≤ (1-1)^2 :=
  boundary_bernoulli_cubic_lower (by decide) (by norm_num) (by norm_num)

-- Omitting the cubic subtraction gives a false lower bound inside the unit interval.
example : ¬ 1-(4 : ℝ)*(1/2)+4*(4-1)/2*(1/2)^2 ≤ (1-1/2)^4 := by
  norm_num

#print axioms permanent_first_column_entropy_lower_bound
#print axioms permanent_boundary_lower_bound
#print axioms boundaryPermanentFloor_eq_gamma_ratio
#print axioms boundary_bernoulli_cubic_lower
#print axioms boundaryPermanentRatio_succ_succ
#print axioms boundaryPermanentRatio_sub_one_lower
#print axioms boundaryPermanentRatio_gap

end DittertRybin.Tests
