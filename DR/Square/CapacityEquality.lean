import DR.Square.CapacityEqualityDeletion
import DR.Square.CapacityEqualityEntropy

/-!
# Equality in van der Waerden's permanent bound

The matrix-specific first-deletion lower bound and strict entropy inequality
force one column to be uniform. Column permutation gives every column. The
zero- and one-dimensional cases are included explicitly.
-/

open scoped BigOperators
open Finset Set Matrix

namespace DittertRybin

theorem first_column_uniform_of_permanent_eq {n : ℕ} (hn : 2 ≤ n + 1)
    {A : Board (n + 1) (n + 1)} (hA : A ∈ doublyStochastic ℝ (Fin (n + 1)))
    (heq : A.permanent = dittertConstant (n + 1)) :
    ∀ i, A i 0 = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  apply (matrixEntropyFactor_le_iff hn (fun i => A i 0)
    (fun i => nonneg_of_mem_doublyStochastic hA) (sum_col_of_mem_doublyStochastic hA 0)).mp
  exact (matrixProduct_first_deletion_capacity hA).trans
    (first_deletion_capacity_le_of_permanent_eq hA heq)

theorem doublyStochastic_permute_second_index {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (e : Equiv.Perm (Fin n)) :
    A.submatrix id e ∈ doublyStochastic ℝ (Fin n) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun i j => nonneg_of_mem_doublyStochastic hA, ?_, ?_⟩
  · intro i
    change ∑ j, A i (e j) = 1
    rw [Equiv.sum_comp e (fun j => A i j), sum_row_of_mem_doublyStochastic hA]
  · intro j
    exact sum_col_of_mem_doublyStochastic hA (e j)

/-- A doubly stochastic matrix attains van der Waerden's lower bound only
when every entry is the uniform value. This includes n=0 and n=1. -/
theorem uniform_of_permanent_eq_dittertConstant {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (heq : A.permanent = dittertConstant n) :
    ∀ i j, A i j = (n : ℝ)⁻¹ := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero =>
      intro i j
      have h := sum_row_of_mem_doublyStochastic hA i
      have hj : j = 0 := by apply Fin.ext; omega
      simpa [hj] using h
    | succ n =>
      intro i j
      let e : Equiv.Perm (Fin (n + 1 + 1)) := Equiv.swap 0 j
      have hB := doublyStochastic_permute_second_index hA e
      have hperm : (A.submatrix id e).permanent = dittertConstant (n + 1 + 1) := by
        rw [Matrix.permanent_permute_rows, heq]
      have hcol := first_column_uniform_of_permanent_eq (by omega) hB hperm i
      simpa [Matrix.submatrix_apply, e] using hcol

/-- Sharp lower bound with its complete equality classification. -/
theorem permanent_eq_dittertConstant_iff {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    A.permanent = dittertConstant n ↔ ∀ i j, A i j = (n : ℝ)⁻¹ := by
  constructor
  · exact uniform_of_permanent_eq_dittertConstant hA
  · intro h
    have heq : A = fun _ _ => (n : ℝ)⁻¹ := by ext i j; exact h i j
    rw [heq, permanent_uniform_square]

theorem vanDerWaerden_with_equality {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    dittertConstant n ≤ A.permanent ∧
      (A.permanent = dittertConstant n ↔ ∀ i j, A i j = (n : ℝ)⁻¹) :=
  ⟨permanent_lower_bound_of_doublyStochastic hA, permanent_eq_dittertConstant_iff hA⟩

end DittertRybin
