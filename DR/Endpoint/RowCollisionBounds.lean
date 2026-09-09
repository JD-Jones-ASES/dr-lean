import DR.Endpoint.RowCollisions
import DR.Endpoint.Contenders
import DR.Square.NormalizedMatrix

/-! Exact collision load and total-mass estimates for the normalized
original-row law. The same generic estimates may be applied to a deleted
board only after separately proving its retained row sums positive. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The self-collision term is removed before computing the graph load. -/
theorem rowCollisionLoad_eq {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) (i : Fin m) :
    rowCollisionLoad X i = ∑ j, X i j*(colSum X j-X i j) := by
  classical
  unfold rowCollisionLoad
  have hp : (∑ h ∈ Finset.univ.erase i, rowCollisionProbability X i h) =
      ∑ h ∈ Finset.univ.erase i, ∑ j, X i j*X h j := by
    apply Finset.sum_congr rfl
    intro h hh
    exact rowCollisionProbability_eq X hs i h (Finset.ne_of_mem_erase hh).symm
  rw [hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum,Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rfl

/-- The factor two is exactly the conversion from ordered to unordered pairs. -/
theorem rowCollisionIntensity_eq {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) :
    2*rowCollisionIntensity X =
      ∑ j, (colSum X j)^2 - ∑ i, ∑ j, (X i j)^2 := by
  unfold rowCollisionIntensity
  simp_rw [rowCollisionLoad_eq X hs]
  have he : (∑ i, ∑ j, X i j*(colSum X j-X i j)) =
      ∑ j, (colSum X j)^2 - ∑ i, ∑ j, (X i j)^2 := by
    simp_rw [mul_sub,← pow_two,Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => X i j*colSum X j)]
    simp only [← Finset.sum_mul,colSum,pow_two]
  rw [← he]
  ring

/-- A common normalized-column cap bounds every incident collision load. -/
theorem rowCollisionLoad_le_column_cap {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i = 1)
    {C : ℝ} (hC : ∀ j, colSum X j ≤ C) (i : Fin m) :
    rowCollisionLoad X i ≤ C := by
  rw [rowCollisionLoad_eq X hs]
  calc
    _ ≤ ∑ j, X i j*C := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith [hC j,hX i j]) (hX i j)
    _ = C := by rw [← Finset.sum_mul,← rowSum,hs,one_mul]

/-- Dropping nonnegative self terms gives the usual total pair-mass upper bound. -/
theorem rowCollisionIntensity_le_column_sq {m n : ℕ} (X : Board m n)
    (hs : ∀ i, rowSum X i = 1) :
    rowCollisionIntensity X ≤ (1/2)*∑ j, (colSum X j)^2 := by
  have he := rowCollisionIntensity_eq X hs
  have hn : 0 ≤ ∑ i, ∑ j, (X i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- Weighted Cauchy retains reciprocal row masses rather than replacing all
of them by the rough minimum-row bound. Zero cells and columns are allowed. -/
theorem normalizeRows_column_sq_le {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) (j : Fin n) :
    (colSum (normalizeRows P) j)^2 ≤
      colSum P j * ∑ i, P i j/(rowSum P i)^2 := by
  have h := weighted_sum_mul_sq_le (fun i => P i j) (fun i => 1/rowSum P i)
    (fun i => hP i j)
  simpa only [one_div,← div_eq_mul_inv,inv_pow,normalizeRows,colSum] using h

/-- Exact reciprocal-mass bound for the actual independent original-row collisions. -/
theorem normalizedRow_collisionIntensity_le {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) (hr : ∀ i, 0 < rowSum P i)
    {C : ℝ} (hC : ∀ j, colSum P j ≤ C) :
    rowCollisionIntensity (normalizeRows P) ≤ (C/2)*∑ i, 1/rowSum P i := by
  have hs := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hsq : (∑ j, (colSum (normalizeRows P) j)^2) ≤
      C*∑ i, 1/rowSum P i := by
    calc
      _ ≤ ∑ j, C*∑ i, P i j/(rowSum P i)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        apply (normalizeRows_column_sq_le P hP j).trans
        exact mul_le_mul_of_nonneg_right (hC j)
          (Finset.sum_nonneg fun i _ => div_nonneg (hP i j) (sq_nonneg _))
      _ = _ := by
        rw [← Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_div,← rowSum]
        field_simp [(hr i).ne']
  have h := (rowCollisionIntensity_le_column_sq _ hs).trans
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 1/2))
  exact h.trans_eq (by ring)

/-- Dividing by each actual row mass retains a common positive lower-row cap. -/
theorem normalizeRows_column_le {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) {rmin : ℝ} (hrmin : 0 < rmin)
    (hr : ∀ i, rmin ≤ rowSum P i) (j : Fin n) :
    colSum (normalizeRows P) j ≤ colSum P j/rmin := by
  unfold colSum normalizeRows
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left (hP i j) hrmin (hr i)

/-- A positive original-row cap and an original-column cap give the graph load. -/
theorem normalizedRow_collisionLoad_le {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) {rmin C : ℝ} (hrmin : 0 < rmin)
    (hr : ∀ i, rmin ≤ rowSum P i) (hC : ∀ j, colSum P j ≤ C) (i : Fin m) :
    rowCollisionLoad (normalizeRows P) i ≤ C/rmin := by
  apply rowCollisionLoad_le_column_cap _ (normalizeRows_nonneg P hP)
    (normalizeRows_rowSum P (fun i => (hrmin.trans_le (hr i)).ne'))
  intro j
  exact (normalizeRows_column_le P hP hrmin hr j).trans
    (div_le_div_of_nonneg_right (hC j) hrmin.le)

/-- Reciprocal deviation of the scaled row masses y_i=m*r_i. -/
noncomputable def endpointRowReciprocalDeviation {m n : ℕ} (P : Board m n) : ℝ :=
  ∑ i, ((m:ℝ)*rowSum P i-1)^2/((m:ℝ)*rowSum P i)

theorem endpointRowReciprocalDeviation_nonneg {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ endpointRowReciprocalDeviation P :=
  Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP i))

/-- The reciprocal identity uses the full row-mass normalization exactly. -/
theorem endpointRowReciprocalDeviation_identity {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (hs : totalMass P = 1) (hr : ∀ i, rowSum P i ≠ 0) :
    (∑ i, 1/rowSum P i) = (m:ℝ)^2+(m:ℝ)*endpointRowReciprocalDeviation P := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he (i : Fin m) :
      (m:ℝ)*(((m:ℝ)*rowSum P i-1)^2/((m:ℝ)*rowSum P i)) =
        (m:ℝ)^2*rowSum P i-2*(m:ℝ)+1/rowSum P i := by
    field_simp [hm0,hr i]
    ring
  unfold endpointRowReciprocalDeviation
  rw [Finset.mul_sum]
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  change (∑ i, 1/rowSum P i) =
    (m:ℝ)^2+((m:ℝ)^2*totalMass P-(∑ _ : Fin m, 2*(m:ℝ))+(∑ i, 1/rowSum P i))
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Source equation (9), with the actual independent original-row collision law. -/
theorem endpoint_original_collisionIntensity_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    {C : ℝ} (hC : ∀ j, colSum P j ≤ C) :
    rowCollisionIntensity (normalizeRows P) ≤
      C*(m:ℝ)^2/2*(1+endpointRowReciprocalDeviation P/(m:ℝ)) := by
  have hr := endpoint_contender_rows_pos hm hmn hP hcont
  have h := normalizedRow_collisionIntensity_le P hP.1 hr hC
  rw [endpointRowReciprocalDeviation_identity (by omega) P hP.2 (fun i => (hr i).ne')] at h
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  apply h.trans_eq
  field_simp

end DittertRybin
