import DR.Endpoint.PermanentCofactorAlgebra
import DR.Endpoint.PermanentFaceDirections
import DR.Endpoint.PositiveMaximizersGeometry

/-! Exact row averaging algebra, including its squared-norm change. -/

namespace DittertRybin
open scoped BigOperators

theorem permanent_updateRow_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i : ι) (u v : ι → ℝ) (s t : ℝ) :
    (A.updateRow i (fun j => s*u j+t*v j)).permanent =
      s*(A.updateRow i u).permanent+t*(A.updateRow i v).permanent := by
  simp only [permanent_updateRow_expansion, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

noncomputable def averagePermanentRows {n : ℕ} (A : Board n n) (a b : Fin n) : Board n n :=
  (A.updateRow a (fun j => (A a j+A b j)/2)).updateRow b
    (fun j => (A a j+A b j)/2)

theorem averagePermanentRows_eq_blend {n : ℕ} (A : Board n n)
    (a b : Fin n) (hab : a ≠ b) :
    averagePermanentRows A a b = (blendColumns A.transpose a b (1/2)).transpose := by
  ext i j
  by_cases hi : i = a <;> by_cases hj : i = b <;>
    simp_all [averagePermanentRows, Matrix.updateRow_apply, blendColumns,
      Matrix.transpose_apply] <;> ring

theorem averagePermanentRows_norm {n : ℕ} (A : Board n n)
    (a b : Fin n) (hab : a ≠ b) :
    orderThreeSquareSum (averagePermanentRows A a b) =
      orderThreeSquareSum A-(1/2)*∑ j, (A a j-A b j)^2 := by
  rw [averagePermanentRows_eq_blend A a b hab, orderThreeSquareSum_transpose,
    orderThreeSquareSum_blendColumns _ a b hab, orderThreeSquareSum_transpose]
  norm_num [Matrix.transpose_apply]

theorem averagePermanentRows_permanent {n : ℕ} (A : Board n n)
    (a b : Fin n) (hab : a ≠ b) :
    (averagePermanentRows A a b).permanent =
      ((A.updateRow b (A a)).permanent+2*A.permanent+
        (A.updateRow a (A b)).permanent)/4 := by
  let w : Fin n → ℝ := fun j => (A a j+A b j)/2
  have hlin (B : Board n n) (i : Fin n) :
      (B.updateRow i w).permanent =
        ((B.updateRow i (A a)).permanent+(B.updateRow i (A b)).permanent)/2 := by
    have hw : w = fun j => (1/2)*A a j+(1/2)*A b j := by ext j; dsimp [w]; ring
    rw [hw, permanent_updateRow_linear]
    ring
  change ((A.updateRow a w).updateRow b w).permanent = _
  rw [hlin]
  have hcomm (v : Fin n → ℝ) :
      (A.updateRow a w).updateRow b v = (A.updateRow b v).updateRow a w := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      simp_all [Matrix.updateRow_apply]
  rw [hcomm, hcomm, hlin, hlin]
  have hba : (A.updateRow b (A a)).updateRow a (A a) = A.updateRow b (A a) := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      simp_all [Matrix.updateRow_apply]
  have haa : A.updateRow a (A a) = A := Matrix.updateRow_eq_self A a
  have hbb : A.updateRow b (A b) = A := Matrix.updateRow_eq_self A b
  have hswap : (A.updateRow b (A a)).updateRow a (A b) =
      A.submatrix (Equiv.swap a b) id := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      simp_all [Matrix.updateRow_apply, Equiv.swap_apply_def]
  rw [hba, hswap, Matrix.permanent_permute_cols, hbb, haa]
  ring

end DittertRybin
