import DR.Endpoint.CollisionSquareCompletion
import Mathlib.Algebra.BigOperators.Fin

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

-- All scalar inequalities can attain the exact stated3/32 margin.
example : (3/32:ℝ)*576 = (1/2)*576+36*2^2-(3/2)*(3*2+8)^2-2*3*(3*2+8) := by norm_num
example : (3/32:ℝ)*576 ≤ (1/2)*576+36*2^2-(3/2)*(3*2+8)^2-2*3*(3*2+8) :=
  endpoint_scalar_completion_gap 3 (3/2) 36 2 8 3 576
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : ¬ ((1/8:ℝ)*576 ≤ (1/2)*576+36*2^2-(3/2)*(3*2+8)^2-2*3*(3*2+8)) := by norm_num

-- Signed zero-sum vectors at the closed v=1/4 boundary are included.
example : (3/32:ℝ)*(∑ i : Fin 3, (![1,-1,0] : Fin 3 → ℝ) i ^ 2) ≤
    quadraticValue (endpointCollisionLowerMatrix (fun _ : Fin 3 => 1/3)
      (fun _ => 0) (fun _ => 1/4) 36) ![1,-1,0] := by
  apply endpoint_collision_lower_matrix_gap (by decide)
  all_goals norm_num [Fin.sum_univ_succ]

-- The zero vector is covered without a strict positivity premise on x.
example {m : ℕ} (hm : 3 ≤ m) (s t v : Fin m → ℝ) (sigma : ℝ)
    (ht : ∀ i, 0 ≤ t i) (he : (∑ i, (1-(m:ℝ)*s i)^2) ≤ 1/9)
    (hmean : (∑ i, t i)/(m:ℝ) ≤ 1/4)
    (hell : (∑ i, (t i-(∑ j, t j)/(m:ℝ))^2) ≤ 1/64)
    (hv : ∀ i, v i ≤ 1/4) (hscale : 4*(m:ℝ)^2 ≤ sigma) :
    0 ≤ quadraticValue (endpointCollisionLowerMatrix s t v sigma) (fun _ => 0) := by
  simpa using endpoint_collision_lower_matrix_gap hm s t v sigma ht he hmean hell hv hscale (fun _ => 0)

-- Losing either the deficit bound or the normalization scale permits a
-- negative actual matrix quadratic, despite all other displayed estimates.
example : quadraticValue (endpointCollisionLowerMatrix (fun _ : Fin 3 => 1/3)
    (fun _ => 0) (fun _ => 1) 36) ![1,-1,0] = -2 := by
  rw [endpointCollisionLowerMatrix_quadratic]
  norm_num [Fin.sum_univ_succ]
example : quadraticValue (endpointCollisionLowerMatrix (fun _ : Fin 3 => 1/3)
    (fun _ => 0) (fun _ => 0) 0) (fun _ => 1) = -6 := by
  rw [endpointCollisionLowerMatrix_quadratic]
  norm_num

#print axioms endpoint_scalar_completion_gap
#print axioms endpointCollisionLowerMatrix_quadratic
#print axioms endpoint_collision_lower_matrix_gap
end DittertRybin.Tests
