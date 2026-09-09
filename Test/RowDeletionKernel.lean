import DR.Endpoint.RowDeletionKernel

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The exact deletion expectation retains the zero diagonal, regardless
-- of normalization, empty columns, or signed row weights.
example {m n : ℕ} (X : Board m n) (i : Fin m) : rowDeletionExpectation X i i=0 := by
  rw [rowDeletionExpectation_eq_event]
  simp

-- Distinct rows use the outside event; there is no extra no-collision
-- condition on the deleted coordinates.
example (X : Board 2 1) : rowDeletionExpectation X 0 1=∏ i,rowSum X i := by
  rw [rowDeletionExpectation_eq_event]
  norm_num
  have he : {z : Fin 2 → Fin 1 | RowsDistinctOutside {0,1} z}=Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    intro i hi
    fin_cases i <;> simp at hi
  rw [he,rowAssignmentEvent_univ,Fin.prod_univ_two]

-- Non-unit mass normalization keeps both powers of h in the denominator.
example : (10:ℝ)^(4-2)*(∏ i : Fin 4, (![1,2,3,4] : Fin 4 → ℝ) i/10)=24/100 := by
  rw [normalizedRow_product_coefficient (by decide) _ 10 (by norm_num)]
  norm_num [Fin.prod_univ_succ]

-- A signed nonzero normalization scale is also valid in the exact algebra.
example : (-10:ℝ)^(4-2)*(∏ i : Fin 4, (![1,2,3,4] : Fin 4 → ℝ) i/(-10))=24/100 := by
  rw [normalizedRow_product_coefficient (by decide) _ (-10) (by norm_num)]
  norm_num [Fin.prod_univ_succ]

-- Dropping h squared fails on the same literal non-unit-mass example.
example : (∏ i : Fin 4, (![1,2,3,4] : Fin 4 → ℝ) i)/(10:ℝ)^2≠
    (∏ i : Fin 4, (![1,2,3,4] : Fin 4 → ℝ) i) := by
  norm_num [Fin.prod_univ_succ]

-- The actual blend identity permits every real vector, with no iid
-- factorial inserted into the independent-row expectation.
example (P : Board 4 5) (hr : ∀ i,rowSum P i≠0) (h : ℝ) (hh : h≠0) (x : Fin 4 → ℝ) :
    quadraticValue (averagingKernel P 2) (fun i => (rowSum P i/h)*x i)=
      averagingCoefficient P 2*(∑ i,(rowSum P i/h)*x i)^2-
      ((∏ i,rowSum P i)/h^2)*quadraticValue (rowDeletionExpectation (normalizeRows P)) x :=
  averagingKernel_normalized_row_quadratic P hr h hh x

#print axioms rowDeletionExpectation_eq_event
#print axioms rowMass_product_delete_pair
#print axioms matchingExclusionKernel_rowMass_conjugacy
#print axioms averagingKernel_rowMass_conjugacy
#print axioms averagingKernel_normalized_row_conjugacy
#print axioms normalizedRow_product_coefficient
#print axioms averagingKernel_normalized_row_quadratic

end DittertRybin.Tests
