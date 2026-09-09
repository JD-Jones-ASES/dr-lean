import DR.Definitions
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Elementary permanent identities and inequalities

These lemmas work directly with Mathlib's sum over permutations. They supply
the finite algebra used in the square proof; no permanent lower-bound theorem
is assumed here. In particular, the block lower bound below retains only
permutations that match each block internally.
-/

open scoped BigOperators
open Finset Equiv Matrix

namespace DittertRybin

section Ordered

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every term defining the permanent of a nonnegative matrix is nonnegative. -/
theorem permanent_nonneg {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ A.permanent :=
  Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun i _ => hA (σ i) i

/-- The permanent is monotone entrywise on nonnegative matrices. -/
theorem permanent_mono {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) :
    A.permanent ≤ B.permanent := by
  apply Finset.sum_le_sum
  intro σ _
  exact Finset.prod_le_prod (fun i _ => hA (σ i) i) (fun i _ => hAB (σ i) i)

end Ordered

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommSemiring R]

/-- A constant matrix has one identical monomial for each permutation. -/
theorem permanent_const (c : R) :
    Matrix.permanent (fun (_ _ : ι) => c) =
      (Fintype.card ι).factorial * c ^ Fintype.card ι := by
  simp [Matrix.permanent, Fintype.card_perm, nsmul_eq_mul]

/-- Scaling each row contributes exactly the product of the row factors. -/
theorem permanent_scale_rows (A : Matrix ι ι R) (r : ι → R) :
    Matrix.permanent (fun i j => r i * A i j) =
      (∏ i, r i) * A.permanent := by
  simp only [Matrix.permanent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]

/-- Scaling each column contributes exactly the product of the column factors. -/
theorem permanent_scale_cols (A : Matrix ι ι R) (c : ι → R) :
    Matrix.permanent (fun i j => A i j * c j) =
      A.permanent * ∏ j, c j := by
  simp only [Matrix.permanent, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  exact Finset.prod_mul_distrib

/-- Independent row and column scaling, with no positivity assumption. -/
theorem permanent_scale_rows_cols (A : Matrix ι ι R) (r c : ι → R) :
    Matrix.permanent (fun i j => r i * A i j * c j) =
      (∏ i, r i) * A.permanent * ∏ j, c j := by
  exact (permanent_scale_cols (fun i j => r i * A i j) c).trans
    (congrArg (fun x => x * ∏ j, c j) (permanent_scale_rows A r))

/-- Multiplication by a diagonal matrix on the left scales the rows. -/
theorem permanent_diagonal_mul (A : Matrix ι ι R) (r : ι → R) :
    (Matrix.diagonal r * A).permanent = (∏ i, r i) * A.permanent := by
  have h : Matrix.diagonal r * A = fun i j => r i * A i j := by
    ext i j
    exact Matrix.diagonal_mul r A i j
  rw [h]
  exact permanent_scale_rows A r

/-- Multiplication by a diagonal matrix on the right scales the columns. -/
theorem permanent_mul_diagonal (A : Matrix ι ι R) (c : ι → R) :
    (A * Matrix.diagonal c).permanent = A.permanent * ∏ j, c j := by
  have h : A * Matrix.diagonal c = fun i j => A i j * c j := by
    ext i j
    exact Matrix.mul_diagonal c A i j
  rw [h]
  exact permanent_scale_cols A c

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Simultaneously relabeling both matrix axes preserves the permanent. -/
theorem permanent_reindex (A : Matrix ι ι R) (e : ι ≃ κ) :
    (A.reindex e e).permanent = A.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e.symm)
  intro σ
  apply Fintype.prod_equiv e.symm
  intro i
  simp [Matrix.reindex_apply, Equiv.permCongr_apply]

/-- In an upper block triangular matrix, a nonzero permutation term must
preserve both blocks. This identity is valid even without an order on R. -/
theorem permanent_fromBlocks_zero_lower
    (A : Matrix ι ι R) (B : Matrix ι κ R) (D : Matrix κ κ R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [Matrix.permanent]
  convert Eq.symm (Finset.sum_subset
    (Finset.subset_univ ((Equiv.Perm.sumCongrHom ι κ).range :
      Set (Equiv.Perm (ι ⊕ κ))).toFinset) ?_) using 1
  · simp_rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    refine Finset.sum_nbij (fun σ : Equiv.Perm ι × Equiv.Perm κ =>
      σ.1.sumCongr σ.2) ?_ ?_ ?_ ?_
    · intro σ _
      rw [Set.mem_toFinset]
      exact ⟨σ, rfl⟩
    · intro σ _ τ _ h
      exact Equiv.Perm.sumCongrHom_injective h
    · intro σ hσ
      rw [Finset.mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨τ, hτ⟩ := hσ
      exact ⟨τ, Finset.mem_univ _, hτ⟩
    · intro σ _
      rw [Fintype.prod_sum_type]
      simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  · intro σ _ hσ
    have hcross : ¬ ∀ i : ι, ∃ j : ι, Sum.inl j = σ (Sum.inl i) := by
      rw [Set.mem_toFinset] at hσ
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index,
        forall_apply_eq_imp_iff] using
        mt Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσ
    obtain ⟨i, hi⟩ := not_forall.mp hcross
    rcases hσi : σ (Sum.inl i) with j | j
    · exact False.elim (hi ⟨j, hσi.symm⟩)
    · apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
      simp only [hσi, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The analogous lower block triangular identity follows by transposition. -/
theorem permanent_fromBlocks_zero_upper
    (A : Matrix ι ι R) (C : Matrix κ ι R) (D : Matrix κ κ R) :
    (Matrix.fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, permanent_fromBlocks_zero_lower,
    Matrix.permanent_transpose, Matrix.permanent_transpose]

/-- In particular, the permanent of two diagonal blocks factors. -/
theorem permanent_fromBlocks_diagonal (A : Matrix ι ι R) (D : Matrix κ κ R) :
    (Matrix.fromBlocks A 0 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero_lower A 0 D

end Algebra

/-- Discarding off-diagonal blocks can only lower the permanent of a
nonnegative matrix. -/
theorem permanent_diagonal_blocks_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hC : ∀ i j, 0 ≤ C i j) (hD : ∀ i j, 0 ≤ D i j) :
    A.permanent * D.permanent ≤ (Matrix.fromBlocks A B C D).permanent := by
  rw [← permanent_fromBlocks_diagonal]
  apply permanent_mono
  · intro i j
    cases i <;> cases j <;> simp [hA, hD]
  · intro i j
    cases i <;> cases j <;> simp [hB, hC]

/-- The permanent constant used in the square normalization is the value
at the matrix whose entries are all 1/n. -/
theorem permanent_uniform_square (n : ℕ) :
    Matrix.permanent (fun (_ _ : Fin n) => (n : ℝ)⁻¹) = dittertConstant n := by
  rw [permanent_const]
  simp [dittertConstant, div_eq_mul_inv, inv_pow]

end DittertRybin
