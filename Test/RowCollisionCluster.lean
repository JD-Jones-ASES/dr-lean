import DR.Endpoint.RowClusterKernel
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- An actual collision-free assignment retains the essential negative
-- all-ones term; dropping it would reverse the inequality on this vector.
example : -quadraticValue (rowDeletionMatrix (fun i : Fin 2 => i)) (fun _ => 1) = -2 := by
  rw [neg_deletion_quadratic_of_injective (show Function.Injective (fun i : Fin 2 => i) from fun _ _ h => h)]
  norm_num
example : ¬((∑ _i : Fin 2,(1:ℝ)^2) ≤
    -quadraticValue (rowDeletionMatrix (fun i : Fin 2 => i)) (fun _ => 1)) := by
  rw [neg_deletion_quadratic_of_injective (show Function.Injective (fun i : Fin 2 => i) from fun _ _ h => h)]
  norm_num

-- The exhaustive pointwise theorem includes an irreparable four-row
-- collision and vectors with mixed signs, with no probability assumptions.
example : rowDeletionMatrix (fun _ : Fin 4 => (0 : Fin 1)) = 0 := by
  have hz : RowClassPattern (Finset.univ : Finset (Fin 4)) (fun _ : Fin 4 => (0 : Fin 1)) := by
    unfold RowClassPattern RowClassEvent RowCollisionEvent
    decide +kernel
  ext i j
  exact hz.deletionMatrix_zero_of_large (by decide) i j
example :
    (if Function.Injective (fun _ : Fin 4 => (0 : Fin 1)) then
      3*(∑ i,(![1,-2,3,-4] : Fin 4 → ℝ) i^2) else 0)-
      2*(∑ i,(![1,-2,3,-4] : Fin 4 → ℝ) i^2)-
      (∑ i,(![1,-2,3,-4] : Fin 4 → ℝ) i)^2 ≤
    -quadraticValue (rowDeletionMatrix (fun _ : Fin 4 => (0 : Fin 1))) ![1,-2,3,-4] :=
  rowDeletion_cluster_pointwise _ _

-- No small-intensity hypothesis is required by the expectation bound.
example (X : Board 3 2) (hX : ∀ i j,0≤X i j) (hs : ∀ i,rowSum X i=1)
    (x : Fin 3 → ℝ) :
    (1-3*rowCollisionIntensity X)*(∑ i,x i^2)-(∑ i,x i)^2 ≤
      -quadraticValue (rowDeletionExpectation X) x :=
  rowDeletion_cluster_intensity_lower X hX hs x
example (X : Board 0 0) (x : Fin 0 → ℝ) :
    (1-3*rowCollisionIntensity X)*(∑ i,x i^2)-(∑ i,x i)^2 ≤
      -quadraticValue (rowDeletionExpectation X) x :=
  rowDeletion_cluster_intensity_lower X (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x

-- Closed D=1/12 and coefficient z=2m² are both accepted, and signed vectors retained.
example (x : Fin 2 → ℝ) :
    (19/36)*(∑ i,x i^2)≤
      8*(∑ i,(1/2:ℝ)*x i)^2+(1-3*(1/12:ℝ))*(∑ i,x i^2)-(∑ i,x i)^2 := by
  apply endpoint_cluster_scalar_gap (fun _ => 1/2) x (1/12) 8
  · norm_num
  · norm_num
  · norm_num
example :
    (19/36)*(∑ i,(![1,-1] : Fin 2 → ℝ) i^2)≤
      8*(∑ i,(1/2:ℝ)*(![1,-1] : Fin 2 → ℝ) i)^2+
      (1-3*(1/12:ℝ))*(∑ i,(![1,-1] : Fin 2 → ℝ) i^2)-
      (∑ i,(![1,-1] : Fin 2 → ℝ) i)^2 := by
  norm_num [Fin.sum_univ_succ]

-- Each substantive scalar hypothesis is necessary for this implication.
example : ¬((19/36)*(2:ℝ)≤0+(1-3*(1:ℝ))*2-0) := by norm_num
example : ¬((19/36)*(2:ℝ)≤0*(1:ℝ)^2+(1-3*(1/12:ℝ))*2-2^2) := by norm_num
example : ¬((19/36)*(2:ℝ)≤8*(0:ℝ)^2+(1-3*(1/12:ℝ))*2-2^2) := by norm_num
example (s : Fin 2 → ℝ) (D z : ℝ) (hs : (∑ i,(1-2*s i)^2)≤1/9)
    (hD : D≤1/12) (hz : 8≤z) :
    (19/36)*(∑ i,(0:Fin 2 → ℝ) i^2)≤
      z*(∑ i,s i*(0:Fin 2 → ℝ) i)^2+
      (1-3*D)*(∑ i,(0:Fin 2 → ℝ) i^2)-(∑ i,(0:Fin 2 → ℝ) i)^2 := by
  apply endpoint_cluster_scalar_gap s 0 D z hs hD
  norm_num at *
  exact hz

#print axioms rowDeletion_cluster_pointwise
#print axioms rowDeletion_cluster_avoidance_lower
#print axioms rowDeletion_cluster_intensity_lower
#print axioms averagingKernel_cluster_lower
#print axioms endpoint_cluster_scalar_gap
#print axioms averagingKernel_cluster_gap
#print axioms averagingKernel_cluster_posDef

end DittertRybin.Tests
