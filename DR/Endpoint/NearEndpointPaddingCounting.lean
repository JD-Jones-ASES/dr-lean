import DR.Endpoint.RowProduct
import Mathlib.GroupTheory.Perm.Fin

/-! Exact codimension-one rook counting and corner-zero bordering. The
identities permit arbitrary signed entries and include a one-cell core. -/
namespace DittertRybin
open scoped BigOperators

/-- Deleting one index enumerates every increasing codimension-one embedding. -/
theorem succAboveOrderEmb_bijective (n : ℕ) :
    Function.Bijective (Fin.succAboveOrderEmb : Fin (n+1) → (Fin n ↪o Fin (n+1))) := by
  classical
  constructor
  · intro i j h
    apply Fin.succAbove_left_injective
    exact congrArg (fun e : Fin n ↪o Fin (n+1) => (e : Fin n → Fin (n+1))) h
  · intro e
    let S := Finset.univ.map e.toEmbedding
    have hS : S.card = n := by simp [S]
    have hc : Sᶜ.card = 1 := by simp [Finset.card_compl, hS]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hSi : S = {i}ᶜ := by
      rw [← hi, compl_compl]
    refine ⟨i, ?_⟩
    rw [← Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
    symm
    apply Finset.orderEmbOfFin_unique'
    intro j
    rw [← hSi]
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩

noncomputable def deletedIndexOrderEmbeddingEquiv (n : ℕ) :
    Fin (n+1) ≃ (Fin n ↪o Fin (n+1)) :=
  Equiv.ofBijective Fin.succAboveOrderEmb (succAboveOrderEmb_bijective n)

@[simp] theorem deletedIndexOrderEmbeddingEquiv_apply {n : ℕ}
    (i : Fin (n+1)) (j : Fin n) : deletedIndexOrderEmbeddingEquiv n i j = i.succAbove j := rfl

/-- A rook placement can equivalently be specified by its row and column
subsets and a bijection between them. -/
theorem rookSum_eq_sum_submatrix_permanent {m n k : ℕ} (P : Board m n) :
    rookSum P k = ∑ r : Fin k ↪o Fin m, ∑ c : Fin k ↪o Fin n,
      Matrix.permanent (fun i j : Fin k => P (r i) (c j)) := by
  classical
  unfold rookSum
  apply Finset.sum_congr rfl
  intro r hr
  rw [← (orderedEmbeddingPermEquiv n k).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c hc
  change (∑ σ : Equiv.Perm (Fin k), ∏ t, P (r t) (c (σ t))) = _
  exact Matrix.permanent_transpose (fun i j : Fin k => P (r i) (c j))

/-- The sum of all single-row, single-column permanent minors is the
codimension-one rook sum, with no extra factorial. -/
theorem rookSum_pred_eq_sum_permanent_minors {n : ℕ} (P : Board (n+1) (n+1)) :
    rookSum P n = ∑ i : Fin (n+1), ∑ j : Fin (n+1), Matrix.permanent (fun r c : Fin n => P (i.succAbove r) (j.succAbove c)) := by
  rw [rookSum_eq_sum_submatrix_permanent,
    ← (deletedIndexOrderEmbeddingEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (deletedIndexOrderEmbeddingEquiv n).sum_comp]
  rfl

/-- Laplace expansion of the permanent along column zero, with increasing
row deletion. The omitted row is retained as an actual physical index. -/
theorem permanent_expand_column_zero {n : ℕ} (A : Board (n+1) (n+1)) :
    A.permanent = ∑ i, A i 0 * Matrix.permanent (fun r c : Fin n => A (i.succAbove r) c.succ) := by
  classical
  rw [Matrix.permanent, ← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, ← Finset.mul_sum]
  congr 1
  cases i using Fin.cases with
  | zero => simp [Matrix.permanent]
  | succ i =>
    simp only [← Fin.succAbove_cycleRange]
    exact Matrix.permanent_permute_cols i.cycleRange
      (fun r c : Fin n => A (i.succ.succAbove r) c.succ)

/-- The corresponding expansion along row zero. -/
theorem permanent_expand_row_zero {n : ℕ} (A : Board (n+1) (n+1)) :
    A.permanent = ∑ j, A 0 j * Matrix.permanent (fun r c : Fin n => A r.succ (j.succAbove c)) := by
  rw [← Matrix.permanent_transpose, permanent_expand_column_zero]
  simp only [Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact Matrix.permanent_transpose _

/-- General signed corner-zero border, placing the new row and column first. -/
def cornerZeroBorder {n : ℕ} (P : Board n n) (c u v : ℝ) : Board (n+1) (n+1) :=
  Fin.cases (Fin.cases 0 (fun _ => u))
    (fun i => Fin.cases v (fun j => c * P i j))

@[simp] theorem cornerZeroBorder_zero_zero {n : ℕ} (P : Board n n) (c u v : ℝ) :
    cornerZeroBorder P c u v 0 0 = 0 := rfl
@[simp] theorem cornerZeroBorder_zero_succ {n : ℕ} (P : Board n n) (c u v : ℝ) (j : Fin n) :
    cornerZeroBorder P c u v 0 j.succ = u := rfl
@[simp] theorem cornerZeroBorder_succ_zero {n : ℕ} (P : Board n n) (c u v : ℝ) (i : Fin n) :
    cornerZeroBorder P c u v i.succ 0 = v := rfl
@[simp] theorem cornerZeroBorder_succ_succ {n : ℕ} (P : Board n n)
    (c u v : ℝ) (i j : Fin n) : cornerZeroBorder P c u v i.succ j.succ = c * P i j := rfl

/-- Exact signed border identity, including the one-cell core and zero scaling. -/
theorem permanent_cornerZeroBorder {n : ℕ} (P : Board (n+1) (n+1)) (c u v : ℝ) :
    (cornerZeroBorder P c u v).permanent = u * v * c^n * rookSum P n := by
  rw [permanent_expand_column_zero, Fin.sum_univ_succ]
  simp only [cornerZeroBorder_zero_zero, cornerZeroBorder_succ_zero, zero_mul, zero_add]
  have hm (i : Fin (n+1)) :
      Matrix.permanent (fun r j : Fin (n+1) => cornerZeroBorder P c u v (i.succ.succAbove r) j.succ) =
        ∑ j : Fin (n+1), u * c^n * Matrix.permanent (fun r s : Fin n => P (i.succAbove r) (j.succAbove s)) := by
    rw [permanent_expand_row_zero
      (fun r j : Fin (n+1) => cornerZeroBorder P c u v (i.succ.succAbove r) j.succ)]
    simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
      cornerZeroBorder_zero_succ, cornerZeroBorder_succ_succ]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Matrix.permanent, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
    ring
  simp_rw [hm]
  rw [rookSum_pred_eq_sum_permanent_minors]
  simp only [← Finset.mul_sum]
  ring

end DittertRybin
