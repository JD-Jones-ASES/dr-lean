import DR.Endpoint.ColumnFailureComparison
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

example : 1-((1:ℝ)*(1+3)/2)*(1/3)≤(Nat.factorial 1:ℝ)*
    elementarySymmetric (fun i : Fin 3 => if i∈({0,1}:Finset (Fin 3)) then 0 else 1/3) 1 := by
  simpa only [Nat.cast_one] using endpoint_deleted_elementary_lower (k:=1)
    (fun _ : Fin 3 => (1/3:ℝ)) (by norm_num) (by norm_num)
    (C:=1/3) (by norm_num) (by norm_num) 0 1 (by decide)

-- Empty outcomes and order zero retain the empty injection.
example : 1-((0:ℝ)*(0+3)/2)*(1/2)≤(Nat.factorial 0:ℝ)*
    elementarySymmetric (fun i : Fin 0 => (Fin.elim0 i : ℝ)) 0 := by
  simpa only [Nat.cast_zero] using endpoint_elementary_lower_two_lost (k:=0)
    (fun i : Fin 0 => (Fin.elim0 i : ℝ)) (fun i => Fin.elim0 i)
    (C:=1/2) (by norm_num) (fun i => Fin.elim0 i) (by norm_num) (by norm_num)

example : (∑ i,(endpointColumnMidpoint (![1,0,0] : Fin 3 → ℝ) 0 1 i)^2)=1/2 := by
  rw [endpointColumnMidpoint_square _ 0 1 (by decide)]
  norm_num [Fin.sum_univ_succ]
example : endpointColumnMidpoint (![0,1] : Fin 2 → ℝ) 0 1=fun _ => 1/2 := by
  funext i
  fin_cases i <;> norm_num [endpointColumnMidpoint]

-- Constant objectives have only ties; the compact theorem does not assume strict gains.
example : (fun _ : Fin 2 → ℝ => (0:ℝ)) (fun _ => 1/2)≤
    (fun _ : Fin 2 → ℝ => (0:ℝ)) ![1,0] := by
  have hx : (![1,0] : Fin 2 → ℝ)∈endpointCappedSimplex 2 1 := by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num
  exact endpoint_midpoint_uniform_comparison (by decide) 1 (fun _ : Fin 2 → ℝ => (0:ℝ))
    continuous_const (fun _ _ _ _ _ => le_rfl) _ hx

-- Without the actual midpoint inequality the uniform comparison is false.
example : ¬-(∑ _i : Fin 2,(1/2:ℝ)^2)≤-(∑ i,((![1,0] : Fin 2 → ℝ) i)^2) := by
  norm_num [Fin.sum_univ_succ]

-- Order two is sharp, including a boundary coordinate equal to zero.
example : (Nat.choose 2 2:ℝ)*(1-((2-2:ℕ):ℝ)*(((2-2:ℕ):ℝ)+3)*1/2)*
    marginalVariance (![1,0] : Fin 2 → ℝ)≤
      endpointColumnFailure 2 (![1,0] : Fin 2 → ℝ)-(1-distinctUniformProbability 2 2) := by
  refine endpoint_column_failure_comparison (by decide) (by decide) _ ?_ ?_ 1 ?_
  · intro i
    fin_cases i <;> norm_num
  · norm_num
  · intro i
    fin_cases i <;> norm_num

-- Negative lower coefficients remain valid when the order exceeds the label count.
example : (Nat.choose 3 2:ℝ)*(1-((3-2:ℕ):ℝ)*(((3-2:ℕ):ℝ)+3)*1/2)*
    marginalVariance (![1,0] : Fin 2 → ℝ)≤
      endpointColumnFailure 3 (![1,0] : Fin 2 → ℝ)-(1-distinctUniformProbability 2 3) := by
  refine endpoint_column_failure_comparison (by decide) (by decide) _ ?_ ?_ 1 ?_
  · intro i
    fin_cases i <;> norm_num
  · norm_num
  · intro i
    fin_cases i <;> norm_num

example : ¬∃ x : Fin 2 → ℝ,x∈endpointCappedSimplex 2 (1/4) := by
  rintro ⟨x,hx⟩
  have hs : (∑ i,x i)≤1/2 := by
    calc
      _≤∑ _i : Fin 2,(1/4:ℝ) := Finset.sum_le_sum (fun i _ => (hx.1 i).2)
      _=_ := by norm_num
  rw [hx.2] at hs
  norm_num at hs

#print axioms endpoint_elementary_lower_two_lost
#print axioms endpoint_deleted_elementary_lower
#print axioms endpointColumnMidpoint_square
#print axioms endpoint_midpoint_uniform_comparison
#print axioms endpointColumnMidpoint_elementary
#print axioms endpointColumnMidpoint_adjusted_failure_le
#print axioms endpoint_column_failure_comparison

end DittertRybin.Tests
