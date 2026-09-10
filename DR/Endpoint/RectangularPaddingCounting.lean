import DR.Endpoint.RowProduct
import Mathlib.Logic.Equiv.Embedding

/-! Exact completion of a rectangular injection by dummy rows. The coefficient
identity permits arbitrary signed weights and empty original/dummy row types. -/
namespace DittertRybin
open scoped BigOperators

/-- Sum over full row assignments by first choosing the original-row injection,
then assigning dummy rows bijectively to its unused columns. -/
theorem sum_embedding_with_constant_rows
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (hcard : Fintype.card γ = Fintype.card α + Fintype.card β)
    (X : α → γ → ℝ) (c : ℝ) :
    (∑ z : α ⊕ β ↪ γ, (∏ i, X i (z (.inl i))) * c ^ Fintype.card β) =
      (Fintype.card β).factorial * c ^ Fintype.card β *
        ∑ e : α ↪ γ, ∏ i, X i (e i) := by
  classical
  let E := (Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := α) (β := β) (γ := γ))
  calc
    _ = ∑ q : (Σ e : α ↪ γ, β ↪ ↥(Set.range e)ᶜ),
        (∏ i, X i (q.1 i)) * c ^ Fintype.card β := by
      apply Fintype.sum_equiv E
      intro z
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
        Fintype.card_compl_set, Fintype.card_range, hcard, Nat.add_sub_cancel_left,
        Nat.descFactorial_self, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- The unused columns and dummy rows have equal size, so every original
injection has exactly the dummy factorial many completions. -/
theorem rectangular_dummy_completion_count {m n : ℕ} (e : Fin m ↪ Fin n) :
    Fintype.card (Fin (n-m) ↪ ↥(Set.range e)ᶜ) = (n-m).factorial := by
  classical
  simp only [Fintype.card_embedding_eq, Fintype.card_compl_set,
    Fintype.card_range, Fintype.card_fin, Nat.descFactorial_self]

/-- Every dummy completion exhausts all unused columns. -/
theorem rectangular_dummy_completion_bijective {m n : ℕ} (e : Fin m ↪ Fin n)
    (f : Fin (n-m) ↪ ↥(Set.range e)ᶜ) : Function.Bijective f := by
  classical
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨f.injective, ?_⟩
  simp only [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_range]

/-- Original rows precede all dummy rows in the padded square. -/
def rectangularPaddingRowEquiv {m n : ℕ} (hmn : m ≤ n) :
    Fin m ⊕ Fin (n-m) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hmn))

@[simp] theorem rectangularPaddingRowEquiv_inl {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    rectangularPaddingRowEquiv hmn (.inl i) = Fin.castLE hmn i := by
  apply Fin.ext
  rfl

@[simp] theorem rectangularPaddingRowEquiv_inr_val {m n : ℕ} (hmn : m ≤ n)
    (i : Fin (n-m)) : (rectangularPaddingRowEquiv hmn (.inr i)).val = m+i.val := rfl

/-- Explicit permutation completion: choose the original injection, then a
bijection of the equally sized dummy-row type into the column complement. -/
noncomputable def rectangularPermutationCompletionEquiv {m n : ℕ} (hmn : m ≤ n) :
    Equiv.Perm (Fin n) ≃ Σ e : Fin m ↪ Fin n, Fin (n-m) ↪ ↥(Set.range e)ᶜ :=
  (Equiv.embeddingEquivOfFinite (Fin n)).symm.trans
    ((Equiv.embeddingCongr (rectangularPaddingRowEquiv hmn).symm (Equiv.refl _)).trans
      Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted)

@[simp] theorem rectangularPermutationCompletionEquiv_original {m n : ℕ} (hmn : m ≤ n)
    (σ : Equiv.Perm (Fin n)) (i : Fin m) :
    (rectangularPermutationCompletionEquiv hmn σ).1 i = σ (Fin.castLE hmn i) := by
  change σ (rectangularPaddingRowEquiv hmn (.inl i)) = _
  rw [rectangularPaddingRowEquiv_inl]

end DittertRybin
