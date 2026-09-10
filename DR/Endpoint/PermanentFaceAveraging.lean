import DR.Endpoint.PermanentRowAveraging
import DR.Endpoint.PermanentAlexandrov
import DR.Endpoint.TwoZeroFaceSupport

/-! Repeated-support averaging at an actual face minimum. The cofactor
comparison and Alexandrov inequality are both previously proved inputs. -/

namespace DittertRybin
open scoped BigOperators

theorem PermanentFaceMinimum.repeated_row_ge {n : ℕ}
    {allowed : Fin n → Fin n → Prop} {A : Board n n}
    (hmin : PermanentFaceMinimum allowed A)
    (hcofactor : ∀ i j, allowed i j → A.permanent ≤ permanentalCofactor A i j)
    (a b : Fin n) (hrows : ∀ j, allowed a j ↔ allowed b j) :
    A.permanent ≤ (A.updateRow b (A a)).permanent := by
  rw [permanent_updateRow_expansion]
  calc
    A.permanent = ∑ j, A a j*A.permanent := by
      rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hmin.1, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hb : allowed b j
      · exact mul_le_mul_of_nonneg_left (hcofactor b j hb)
          (nonneg_of_mem_doublyStochastic hmin.1)
      · have ha : ¬allowed a j := fun h => hb ((hrows j).mp h)
        rw [hmin.2.1 a j ha]
        simp

theorem PermanentFaceMinimum.average_rows_permanent {n : ℕ}
    {allowed : Fin (n+2) → Fin (n+2) → Prop} {A : Board (n+2) (n+2)}
    (hmin : PermanentFaceMinimum allowed A)
    (hcofactor : ∀ i j, allowed i j → A.permanent ≤ permanentalCofactor A i j)
    (a b : Fin (n+2)) (hab : a ≠ b) (hrows : ∀ j, allowed a j ↔ allowed b j) :
    (averagePermanentRows A a b).permanent = A.permanent := by
  have hp : 0 < A.permanent :=
    (dittertConstant_pos (by omega : 0 < n+2)).trans_le
      (permanent_lower_bound_of_doublyStochastic hmin.1)
  have hleft := hmin.repeated_row_ge hcofactor a b hrows
  have hright := hmin.repeated_row_ge hcofactor b a (fun j => (hrows j).symm)
  have hprod := permanent_alexandrov_rows (A := A)
    (fun i j => nonneg_of_mem_doublyStochastic hmin.1) a b
  have hdiff : 0 ≤ ((A.updateRow b (A a)).permanent-A.permanent)*
      ((A.updateRow a (A b)).permanent-A.permanent) := by positivity
  have hsum : (A.updateRow b (A a)).permanent+(A.updateRow a (A b)).permanent =
      2*A.permanent := by nlinarith
  rw [averagePermanentRows_permanent A a b hab]
  linarith

theorem averagePermanentRows_mem_face {n : ℕ}
    {allowed : Fin n → Fin n → Prop} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hz : ∀ i j, ¬allowed i j → A i j = 0)
    (a b : Fin n) (hab : a ≠ b) (hrows : ∀ j, allowed a j ↔ allowed b j) :
    averagePermanentRows A a b ∈ doublyStochastic ℝ (Fin n) ∧
      ∀ i j, ¬allowed i j → averagePermanentRows A a b i j = 0 := by
  let σ := Equiv.swap a b
  have heq : averagePermanentRows A a b =
      (1/2 : ℝ) • A+(1/2 : ℝ) • A.submatrix σ id := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      simp_all [averagePermanentRows, Matrix.updateRow_apply, Matrix.submatrix_apply,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, σ, Equiv.swap_apply_def] <;> ring
  have hperm : A.submatrix σ id ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => nonneg_of_mem_doublyStochastic hA,
      fun i => sum_row_of_mem_doublyStochastic hA (σ i), ?_⟩
    intro j
    change (∑ i, A (σ i) j) = 1
    rw [Equiv.sum_comp σ (fun i => A i j)]
    exact sum_col_of_mem_doublyStochastic hA j
  constructor
  · rw [heq]
    exact convex_doublyStochastic hA hperm (by norm_num) (by norm_num) (by norm_num)
  · intro i j hij
    have hs : A (σ i) j = 0 := by
      apply hz
      by_cases hi : i = a
      · subst i
        simpa [σ] using (fun hb => hij ((hrows j).mpr hb) : ¬allowed b j)
      by_cases hi' : i = b
      · subst i
        simpa [σ] using (fun ha => hij ((hrows j).mp ha) : ¬allowed a j)
      simpa [σ, Equiv.swap_apply_def, hi, hi'] using hij
    rw [heq]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, hz i j hij, hs]

end DittertRybin
