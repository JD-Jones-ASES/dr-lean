import DR.Endpoint.RowDeletionExpectation
import DR.Endpoint.RowCollisionUnion
import DR.Endpoint.RowDeletionKernel

/-!
# The actual collision-cluster bound for two-row deletion

The exhaustive assignment classification gives `E[-L] ≥ (1 - 3D)I - J`,
where `D` is the expected number of colliding row pairs. This is the matrix
input of P0174 `ENDPOINT_COLLISION_CLUSTER_STRIPS.md`, section 4. The law is
one independent column choice per row; applying it to a retained board uses
that board's own normalized row law.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

private theorem cluster_incidence_sq_bounds {m : ℕ} (V : Finset (Fin m))
    (x : Fin m → ℝ) :
    0 ≤ (∑ i, rowClassIncidence V i*x i^2) ∧
      (∑ i, rowClassIncidence V i*x i^2) ≤ ∑ i,x i^2 := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    by_cases hv : i∈V <;> simp [rowClassIncidence,hv,sq_nonneg]
  · apply Finset.sum_le_sum
    intro i hi
    by_cases hv : i∈V <;> simp [rowClassIncidence,hv,sq_nonneg]

/-- A pointwise bound before taking any expectation. No normalization,
nonnegativity, or restriction on the real test vector is involved. -/
theorem rowDeletion_cluster_pointwise {m n : ℕ} (z : Fin m → Fin n)
    (x : Fin m → ℝ) :
    (if Function.Injective z then 3*(∑ i,x i^2) else 0) -
      2*(∑ i,x i^2) - (∑ i,x i)^2 ≤
        -quadraticValue (rowDeletionMatrix z) x := by
  classical
  have hs : 0≤∑ i,x i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  by_cases hi : Function.Injective z
  · rw [if_pos hi,neg_deletion_quadratic_of_injective hi]
    linarith
  rw [if_neg hi]
  rcases rowDeletionMatrix_zero_or_pattern z with hz | hz | hp | ht | ht
  · simp only [hz,quadraticValue,Matrix.zero_apply,mul_zero,zero_mul,
      Finset.sum_const_zero,neg_zero]
    nlinarith [sq_nonneg (∑ i,x i)]
  · exact (hi hz).elim
  · obtain ⟨V,hV,hz⟩ := hp
    rw [hz.neg_deletion_quadratic_pair hV]
    have hv := (cluster_incidence_sq_bounds V x).1
    nlinarith [sq_nonneg ((∑ i,x i) - ∑ i,rowClassIncidence V i*x i)]
  · obtain ⟨V,hV,hz⟩ := ht
    have hv := (cluster_incidence_sq_bounds V x).2
    have hq := hz.neg_deletion_quadratic_triple hV x
    nlinarith [sq_nonneg (∑ i,x i)]
  · obtain ⟨V,W,hV,hW,hd,hz⟩ := ht
    have hv := (cluster_incidence_sq_bounds (V∪W) x).2
    have hq := hz.neg_deletion_quadratic_two_pairs hV hW hd x
    nlinarith [sq_nonneg (∑ i,x i)]

/-- The exact avoidance version is slightly stronger than the intensity
bound. Zero row weights are allowed inside each normalized row. -/
theorem rowDeletion_cluster_avoidance_lower {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (hs : ∀ i,rowSum X i=1) (x : Fin m → ℝ) :
    (3*rowAvoidance X-2)*(∑ i,x i^2) - (∑ i,x i)^2 ≤
      -quadraticValue (rowDeletionExpectation X) x := by
  classical
  have h := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (rowDeletion_cluster_pointwise z x)
      (rowAssignmentMass_nonneg X hX z))
  have hinj := rowAssignment_injective_indicator X (3*∑ i,x i^2)
  have hmass : (∑ z : Fin m → Fin n,rowAssignmentMass X z)=1 := by
    rw [sum_rowAssignmentMass]
    simp [hs]
  have hr : (∑ z : Fin m → Fin n,rowAssignmentMass X z*
      (-quadraticValue (rowDeletionMatrix z) x)) =
      -quadraticValue (rowDeletionExpectation X) x := by
    rw [quadraticValue_rowDeletionExpectation]
    simp only [mul_neg,Finset.sum_neg_distrib]
  simp only [mul_sub,Finset.sum_sub_distrib] at h
  rw [hinj,← Finset.sum_mul,← Finset.sum_mul,hmass,hr] at h
  nlinarith

/-- The collision-cluster matrix inequality for the actual row law.
There is no assumption that the collision intensity is small. -/
theorem rowDeletion_cluster_intensity_lower {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (hs : ∀ i,rowSum X i=1) (x : Fin m → ℝ) :
    (1-3*rowCollisionIntensity X)*(∑ i,x i^2) - (∑ i,x i)^2 ≤
      -quadraticValue (rowDeletionExpectation X) x := by
  have hp := one_sub_rowAvoidance_le_intensity X hX hs
  have hq := rowDeletion_cluster_avoidance_lower X hX hs x
  have hsq : 0≤∑ i,x i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  nlinarith [mul_nonneg (show 0≤rowCollisionIntensity X-(1-rowAvoidance X) by linarith) hsq]

/-- Congruence to the actual retained-board averaging kernel. `h` can be
any positive scale; choosing the retained mass produces the normalized
row vector. The expected collision count uses this board's row law. -/
theorem averagingKernel_cluster_lower {m n : ℕ} (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i)
    (h : ℝ) (hh : 0<h) (x : Fin m → ℝ) :
    averagingCoefficient P (m-2)*(∑ i,(rowSum P i/h)*x i)^2 +
      ((∏ i,rowSum P i)/h^2)*
        ((1-3*rowCollisionIntensity (normalizeRows P))*(∑ i,x i^2)-(∑ i,x i)^2) ≤
      quadraticValue (averagingKernel P (m-2)) (fun i => (rowSum P i/h)*x i) := by
  have hnorm := normalizeRows_nonneg P hP
  have hs := normalizeRows_rowSum P (fun i => ne_of_gt (hr i))
  have hc := rowDeletion_cluster_intensity_lower (normalizeRows P) hnorm hs x
  have hg : 0≤(∏ i,rowSum P i)/h^2 := div_nonneg
    (Finset.prod_nonneg (fun i _ => le_of_lt (hr i))) (sq_nonneg h)
  rw [averagingKernel_normalized_row_quadratic P (fun i => ne_of_gt (hr i)) h hh.ne']
  nlinarith [mul_le_mul_of_nonneg_left hc hg]

end DittertRybin
