import DR.Endpoint.TwoZeroMixedCoefficients
import Mathlib.Logic.Equiv.Fintype

/-! The actual repeated-row permanent inequality for any selected pair.
The finite relabeling preserves the entire matrix, including all zeros. -/

namespace DittertRybin

theorem permanent_repeat_row_permute {n : ℕ} (A : Board n n)
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    ((A.submatrix σ id).updateRow b ((A.submatrix σ id) a)).permanent =
      (A.updateRow (σ b) (A (σ a))).permanent := by
  have heq : (A.submatrix σ id).updateRow b ((A.submatrix σ id) a) =
      (A.updateRow (σ b) (A (σ a))).submatrix σ id := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply]
    by_cases h : i = b
    · simp [h]
    · simp [h, σ.injective.ne h]
  rw [heq, Matrix.permanent_permute_cols]

theorem permanent_alexandrov_rows {n : ℕ} {A : Board (n+2) (n+2)}
    (hA : ∀ i j, 0 ≤ A i j) (a b : Fin (n+2)) :
    (A.updateRow b (A a)).permanent*(A.updateRow a (A b)).permanent ≤ A.permanent^2 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [Matrix.updateRow_eq_self]
    exact le_of_eq (pow_two _).symm
  let f : Fin 2 → Fin (n+2) := Fin.natAdd n
  let g : Fin 2 → Fin (n+2) := ![a,b]
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    omega
  have hg : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have h0 : σ (Fin.natAdd n 0) = a := by simpa [f,g] using hσ 0
  have h1 : σ (Fin.natAdd n 1) = b := by simpa [f,g] using hσ 1
  have h := permanent_repeated_rows_inequality (A := A.submatrix σ id)
    (fun i j => hA (σ i) j)
  rw [permanent_repeat_row_permute, permanent_repeat_row_permute,
    Matrix.permanent_permute_cols, h0, h1] at h
  exact h

end DittertRybin
