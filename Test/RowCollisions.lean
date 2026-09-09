import DR.Endpoint.RowCollisionContenders

namespace DittertRybin.Tests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private def signedRows : Board 2 2 := ![![2,-1],![3,-2]]
private theorem signedRows_sum (i : Fin 2) : rowSum signedRows i = 1 := by
  fin_cases i <;> norm_num [rowSum,signedRows,Fin.sum_univ_two]

-- Independence is row by row, and the algebra permits signed row weights.
example : rowCollisionProbability signedRows 0 1 = 8 := by
  rw [rowCollisionProbability_eq signedRows signedRows_sum 0 1 (by decide)]
  norm_num [signedRows,Fin.sum_univ_two]

-- A row paired with itself has probability one, not its row square sum five.
example : rowCollisionProbability signedRows 0 0 = 1 :=
  rowCollisionProbability_self signedRows signedRows_sum 0
example : rowCollisionProbability signedRows 0 0 ≠ ∑ j, signedRows 0 j*signedRows 0 j := by
  rw [rowCollisionProbability_self signedRows signedRows_sum]
  norm_num [signedRows,Fin.sum_univ_two]

private def sameRows : Board 3 2 := fun _ => ![1,0]
private theorem sameRows_sum (i : Fin 3) : rowSum sameRows i = 1 := by
  norm_num [rowSum,sameRows,Fin.sum_univ_two]

-- Three colliding rows have three unordered edges, rather than six or one.
example : rowCollisionIntensity sameRows = 3 := by
  have h := rowCollisionIntensity_eq sameRows sameRows_sum
  norm_num [colSum,sameRows,Fin.sum_univ_succ] at h
  linarith

private def zeroLastRow : Board 3 2 := ![![1,0],![1,0],![0,0]]
private theorem zeroLastRow_nonneg (i : Fin 3) (j : Fin 2) : 0 ≤ zeroLastRow i j := by
  fin_cases i <;> fin_cases j <;> norm_num [zeroLastRow]

-- Omitting normalization of another row destroys the two-coordinate formula.
example : rowCollisionProbability zeroLastRow 0 1 = 0 := by
  have h0 := rowCollisionProbability_nonneg zeroLastRow zeroLastRow_nonneg 0 1
  have h1 := rowAssignmentEvent_le_total zeroLastRow zeroLastRow_nonneg
    {z | z (0:Fin 3)=z 1}
  change rowCollisionProbability zeroLastRow 0 1 ≤ _ at h1
  norm_num [rowSum,zeroLastRow,Fin.sum_univ_succ,Fin.prod_univ_succ] at h1
  change rowCollisionProbability zeroLastRow 0 1 ≤ 0 at h1
  exact le_antisymm h1 h0
example : (∑ j, zeroLastRow 0 j*zeroLastRow 1 j) = 1 := by
  norm_num [zeroLastRow,Fin.sum_univ_two]

private noncomputable def unequalMass : Board 2 2 := Matrix.diagonal ![(1/4:ℝ),3/4]

-- The reciprocal correction records unequal positive row masses exactly.
example : endpointRowReciprocalDeviation unequalMass = 2/3 := by
  norm_num [endpointRowReciprocalDeviation,unequalMass,rowSum,Matrix.diagonal_apply,
    Fin.sum_univ_succ]
example : (∑ i, 1/rowSum unequalMass i) = 16/3 := by
  norm_num [unequalMass,rowSum,Matrix.diagonal_apply,Fin.sum_univ_succ]

-- Zero cells and zero columns are included in the actual normalized cap.
example (P : Board 3 7) (hP : ∀ i j, 0 ≤ P i j)
    (hr : ∀ i, 0 < rowSum P i) (hC : ∀ j, colSum P j ≤ 1/5) :
    rowCollisionIntensity (normalizeRows P) ≤ (1/10)*∑ i, 1/rowSum P i := by
  have h := normalizedRow_collisionIntensity_le P hP hr hC
  norm_num at h
  simpa only [one_div] using h

-- An empty independent assignment avoids collisions and has no edges.
example : rowCollisionIntensity (0 : Board 0 0) = 0 := by
  simp [rowCollisionIntensity]
example : 1-rowAvoidance (0 : Board 0 0) ≤ rowCollisionIntensity (0 : Board 0 0) := by
  apply one_sub_rowAvoidance_le_intensity
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

-- The strip inputs are derived from an actual contender, without a row-law premise.
example {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n) (P : Board m n)
    (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (i : Fin m) :
    rowCollisionLoad (normalizeRows P) i ≤
      3*(m:ℝ)*(1/(n:ℝ)+1/(m:ℝ)^4)/(1-distinctUniformProbability n m) :=
  endpoint_original_collisionLoad_large hm hmn hP hcont i

#print axioms endpoint_original_collisionIntensity_large
#print axioms endpoint_original_collisionLoad_large
#print axioms endpoint_original_avoidance_lower_union
#print axioms rowAssignmentEvent_coordinate_constraints
#print axioms rowAssignmentEvent_two_coordinates
#print axioms rowCollisionProbability_eq
#print axioms rowCollisionIntensity_eq
#print axioms normalizedRow_collisionIntensity_le
#print axioms endpoint_original_collisionIntensity_le
#print axioms rowCollisionIntensity_eq_sum_lt
#print axioms one_sub_rowAvoidance_le_intensity

end DittertRybin.Tests
