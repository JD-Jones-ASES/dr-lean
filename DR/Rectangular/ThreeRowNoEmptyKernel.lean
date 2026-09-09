import DR.Rectangular.ThreeRowAveraging

/-! The first-order residual kernel is nonnegative and has the full remaining mass on its diagonal. -/

namespace DittertRybin
open scoped BigOperators

theorem rookSum_one (P : Board m n) : rookSum P 1 = totalMass P := by
  have h := eventMass_rows_cols_eq_factorial_rook (k := 1) P
  have hset : {s : Fin 1 → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨Function.injective_of_subsingleton _, Function.injective_of_subsingleton _⟩
  rw [hset, eventMass_univ, sum_cell_weights, pow_one] at h
  simpa using h.symm

theorem averagingCoefficient_one (P : Board m n) : averagingCoefficient P 1 = totalMass P := by
  have h := eventMass_cols_eq_factorial_elementary (k := 1) P
  have hset : {s : Fin 1 → Fin m × Fin n | ColsDistinct s} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Function.injective_of_subsingleton _
  rw [hset, eventMass_univ, sum_cell_weights, pow_one] at h
  simpa only [averagingCoefficient, Nat.factorial_one, Nat.cast_one, one_mul] using h.symm

theorem totalMass_eraseRows_le {m n : ℕ} {P : Board m n} (hP : ∀ i j, 0 ≤ P i j)
    (S : Finset (Fin m)) : totalMass (eraseRows P S) ≤ totalMass P := by
  unfold totalMass rowSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hi : i ∈ S
  · simpa only [eraseRows, if_pos hi] using hP i j
  · simp only [eraseRows, if_neg hi, le_refl]

theorem averagingKernel_one_diagonal (P : Board m n) (i : Fin m) :
    averagingKernel P 1 i i = totalMass P := by
  simp [averagingKernel, matchingExclusionKernel, averagingCoefficient_one]

theorem averagingKernel_one_nonneg {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (i h : Fin m) : 0 ≤ averagingKernel P 1 i h := by
  by_cases hih : i = h
  · subst h
    rw [averagingKernel_one_diagonal]
    exact Finset.sum_nonneg fun i _ => rowSum_nonneg hP i
  · simp only [averagingKernel, matchingExclusionKernel, if_neg hih, averagingCoefficient_one,
      rookSum_one]
    exact sub_nonneg.mpr (totalMass_eraseRows_le hP {i, h})

theorem averagingKernel_one_quadratic_nonneg {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ ∑ i, ∑ h, v i * averagingKernel P 1 i h * v h := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun h _ =>
    mul_nonneg (mul_nonneg (hv i) (averagingKernel_one_nonneg hP i h)) (hv h)

/-- A positive coordinate and positive remaining mass make the diagonal term strictly positive. -/
theorem averagingKernel_one_quadratic_pos {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (hMass : 0 < totalMass P)
    (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) (i : Fin m) (hi : 0 < v i) :
    0 < ∑ i, ∑ h, v i * averagingKernel P 1 i h * v h := by
  have hterm (a b : Fin m) : 0 ≤ v a * averagingKernel P 1 a b * v b :=
    mul_nonneg (mul_nonneg (hv a) (averagingKernel_one_nonneg hP a b)) (hv b)
  have hdiag : 0 < v i * averagingKernel P 1 i i * v i := by
    rw [averagingKernel_one_diagonal]
    exact mul_pos (mul_pos hi hMass) hi
  apply lt_of_lt_of_le hdiag
  calc
    _ ≤ ∑ h, v i * averagingKernel P 1 i h * v h :=
      Finset.single_le_sum (fun h _ => hterm i h) (Finset.mem_univ i)
    _ ≤ ∑ a, ∑ h, v a * averagingKernel P 1 a h * v h :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun h _ => hterm a h) (Finset.mem_univ i)

theorem eraseColumns_nonneg {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (S : Finset (Fin n)) : ∀ i j, 0 ≤ eraseColumns P S i j := by
  intro i j
  by_cases hj : j ∈ S
  · simp only [eraseColumns, if_pos hj, le_refl]
  · simpa only [eraseColumns, if_neg hj] using hP i j

/-- Splitting into an empty column cannot decrease the actual three-sample probability. -/
theorem separationProbability_split_zero_column {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n) (hab : a ≠ b) (ha : ∀ i, P i a = 0) :
    separationProbability P 3 ≤ separationProbability (blendColumns P a b (1 / 2)) 3 := by
  have hquad := averagingKernel_one_quadratic_nonneg (eraseColumns_nonneg hP {a, b})
    (fun i => P i b) (fun i => hP i b)
  have h := separationProbability_blend_identity (k := 1) P a b hab (1 / 2)
  simp only [ha, zero_sub, neg_mul, mul_neg, neg_neg] at h
  norm_num at h
  linarith only [h, hquad]

/-- The gain is strict as soon as the donor and another column both carry positive mass. -/
theorem separationProbability_split_zero_column_strict {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n) (hab : a ≠ b) (ha : ∀ i, P i a = 0)
    (hMass : 0 < totalMass (eraseColumns P {a, b})) (i : Fin m) (hi : 0 < P i b) :
    separationProbability P 3 < separationProbability (blendColumns P a b (1 / 2)) 3 := by
  have hquad := averagingKernel_one_quadratic_pos (eraseColumns_nonneg hP {a, b}) hMass
    (fun i => P i b) (fun i => hP i b) i hi
  have h := separationProbability_blend_identity (k := 1) P a b hab (1 / 2)
  simp only [ha, zero_sub, neg_mul, mul_neg, neg_neg] at h
  norm_num at h
  linarith only [h, hquad]

/-- Every feasible split of an empty column at a global maximizer is again globally maximal. -/
theorem IsSeparationGlobalMax.split_zero_column {m n : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (a b : Fin n) (hab : a ≠ b) (ha : ∀ i, P i a = 0) :
    IsSeparationGlobalMax (blendColumns P a b (1 / 2)) 3 := by
  intro Q hQ
  exact (hmax Q hQ).trans (separationProbability_split_zero_column hP.1 a b hab ha)

end DittertRybin
