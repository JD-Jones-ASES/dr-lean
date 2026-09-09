import DR.Endpoint.ColumnRigidity
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- One-sided rigidity includes the narrow n=1 host, even when n<m.
example : UniformMaximizer 2 1 2 := by
  apply uniform_maximizer_endpoint_of_column_rigidity (by decide) (by decide)
  intro P _ _ i a b
  exact congrArg (P i) (Subsingleton.elim a b)

private noncomputable def zeroRowBoard : Board 2 3 := fun i _ => if i=0 then 1/3 else 0

private theorem zeroRowBoard_probability : IsProbability zeroRowBoard := by
  constructor
  · intro i j
    fin_cases i <;> norm_num [zeroRowBoard]
  · norm_num [totalMass,rowSum,zeroRowBoard,Fin.sum_univ_succ]

-- Equal columns do not by themselves force uniform rows. The exact product
-- formula remains valid at a zero row, and the contender premise excludes it.
example : separationProbability zeroRowBoard 2 = 2/3 := by
  rw [endpoint_equal_columns_separation (by decide) zeroRowBoard zeroRowBoard_probability
    (fun _ _ _ => rfl)]
  norm_num [rowSum,zeroRowBoard,Fin.sum_univ_succ,Fin.prod_univ_two,
    distinctUniformProbability,Nat.descFactorial]

example : ¬(separationProbability (uniformBoard 2 3) 2 ≤
    separationProbability zeroRowBoard 2) := by
  intro hcont
  have he := endpoint_equal_columns_contender_uniform (by decide) (by decide)
    zeroRowBoard zeroRowBoard_probability (fun _ _ _ => rfl) hcont
  have hh := congrFun (congrFun he 1) 0
  norm_num [zeroRowBoard,uniformBoard] at hh

-- Order one has many maximizers; the m≥2 hypothesis is necessary.
example : ¬UniformMaximizer 1 2 1 := by
  intro hmax
  let P : Board 1 2 := fun _ j => if j=0 then 1 else 0
  have hP : IsProbability P := by
    constructor
    · intro i j
      fin_cases j <;> norm_num [P]
    · norm_num [totalMass,rowSum,P,Fin.sum_univ_succ]
  have hv : separationProbability P 1 = uniformSeparationValue 1 2 1 := by
    rw [separationProbability_one hP]
    norm_num [uniformSeparationValue,distinctUniformProbability,Nat.descFactorial]
  have he := (hmax P hP).2.mp hv
  have hh := congrFun (congrFun he 0) 1
  norm_num [P,uniformBoard] at hh

#print axioms endpoint_equal_columns_entries
#print axioms endpoint_equal_columns_separation
#print axioms endpoint_factorial_rowProduct
#print axioms endpoint_equal_columns_contender_uniform
#print axioms uniform_maximizer_endpoint_of_column_rigidity
end DittertRybin.Tests
