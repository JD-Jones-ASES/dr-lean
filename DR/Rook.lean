import DR.EndpointIdentity
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Elementary symmetric sums and weighted rook placements

Increasing index embeddings enumerate subsets exactly once. A rook
placement is enumerated by its increasing row labels and distinct column
labels, so it is counted once rather than once per ordering of its rooks.
Sorting the row indices of an arbitrary embedding produces an independent
permutation of the sample indices. This proves the factorial normalization
in the general semimatching identity by an explicit equivalence.
-/

namespace DittertRybin

open scoped BigOperators

/-- A subset product, enumerating its labels in increasing order. -/
noncomputable def elementarySymmetric {d : ℕ} (x : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ e : Fin k ↪o Fin d, ∏ t, x (e t)

/-- Sum of products over all k-rook placements, with canonical increasing row order. -/
noncomputable def rookSum {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  ∑ r : Fin k ↪o Fin m, ∑ c : Fin k ↪ Fin n, ∏ t, P (r t) (c t)

/-- Forget increasing order after permuting the sample positions. -/
def orderedEmbeddingWithPerm {d k : ℕ}
    (q : (Fin k ↪o Fin d) × Equiv.Perm (Fin k)) : Fin k ↪ Fin d :=
  q.2.toEmbedding.trans q.1.toEmbedding

private def embeddingFinset {d k : ℕ} (e : Fin k ↪ Fin d) : Finset (Fin d) :=
  Finset.univ.map e

private theorem embeddingFinset_card {d k : ℕ} (e : Fin k ↪ Fin d) :
    (embeddingFinset e).card = k := by simp [embeddingFinset]

private theorem mem_embeddingFinset {d k : ℕ} (e : Fin k ↪ Fin d) (i : Fin k) :
    e i ∈ embeddingFinset e := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem orderedEmbeddingWithPerm_injective {d k : ℕ} :
    Function.Injective (orderedEmbeddingWithPerm (d := d) (k := k)) := by
  rintro ⟨r, π⟩ ⟨s, σ⟩ h
  let e := orderedEmbeddingWithPerm (r, π)
  have hr (i : Fin k) : r i ∈ embeddingFinset e := by
    have hm := mem_embeddingFinset e (π.symm i)
    change r (π (π.symm i)) ∈ embeddingFinset e at hm
    simpa only [Equiv.apply_symm_apply] using hm
  have hs (i : Fin k) : s i ∈ embeddingFinset e := by
    have hm := mem_embeddingFinset e (σ.symm i)
    have heq : e = orderedEmbeddingWithPerm (s, σ) := h
    have hh : e (σ.symm i) = s i := by
      rw [heq]
      change s (σ (σ.symm i)) = s i
      rw [Equiv.apply_symm_apply]
    rwa [hh] at hm
  have hrs : r = s :=
    (Finset.orderEmbOfFin_unique' (embeddingFinset_card e) hr).trans
      (Finset.orderEmbOfFin_unique' (embeddingFinset_card e) hs).symm
  subst s
  have hπσ : π = σ := by
    apply Equiv.ext
    intro i
    apply r.injective
    exact congrArg (fun f : Fin k ↪ Fin d ↦ f i) h
  subst σ
  rfl

theorem orderedEmbeddingWithPerm_surjective {d k : ℕ} :
    Function.Surjective (orderedEmbeddingWithPerm (d := d) (k := k)) := by
  intro e
  let S := embeddingFinset e
  let er : Fin k ≃ S := Equiv.ofBijective
    (fun i ↦ (⟨e i, mem_embeddingFinset e i⟩ : S)) (by
      constructor
      · intro i j h
        exact e.injective (congrArg Subtype.val h)
      · intro a
        obtain ⟨i, _, hi⟩ := Finset.mem_map.mp a.property
        exact ⟨i, Subtype.ext hi⟩)
  let r := S.orderEmbOfFin (embeddingFinset_card e)
  let π := er.trans (S.orderIsoOfFin (embeddingFinset_card e)).symm.toEquiv
  refine ⟨(r, π), ?_⟩
  apply Function.Embedding.ext
  intro i
  have h := (S.orderIsoOfFin (embeddingFinset_card e)).apply_symm_apply (er i)
  exact congrArg Subtype.val h

/-- Sorting an injection records one increasing embedding and one permutation. -/
noncomputable def orderedEmbeddingPermEquiv (d k : ℕ) :
    ((Fin k ↪o Fin d) × Equiv.Perm (Fin k)) ≃ (Fin k ↪ Fin d) :=
  Equiv.ofBijective orderedEmbeddingWithPerm
    ⟨orderedEmbeddingWithPerm_injective, orderedEmbeddingWithPerm_surjective⟩

/-- Each subset product occurs exactly k! times among injective ordered samples. -/
theorem sum_embeddings_eq_factorial_elementary {d k : ℕ} (x : Fin d → ℝ) :
    (∑ e : Fin k ↪ Fin d, ∏ t, x (e t)) = (k.factorial : ℝ) * elementarySymmetric x k := by
  rw [← (orderedEmbeddingPermEquiv d k).sum_comp]
  rw [Fintype.sum_prod_type]
  have hprod (r : Fin k ↪o Fin d) (π : Equiv.Perm (Fin k)) :
      (∏ t, x (orderedEmbeddingPermEquiv d k (r, π) t)) = ∏ t, x (r t) :=
    Equiv.prod_comp π (fun t ↦ x (r t))
  simp_rw [hprod]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rfl

/-- Relabeling sample positions does not change the sum over column injections. -/
theorem sum_column_embeddings_permuted {m n k : ℕ} (P : Board m n)
    (r : Fin k → Fin m) (π : Equiv.Perm (Fin k)) :
    (∑ c : Fin k ↪ Fin n, ∏ t, P (r (π t)) (c t)) =
      ∑ c : Fin k ↪ Fin n, ∏ t, P (r t) (c t) := by
  apply Fintype.sum_equiv (Equiv.embeddingCongr π (Equiv.refl (Fin n)))
  intro c
  change (∏ t, P (r (π t)) (c t)) = ∏ t, P (r t) (c (π.symm t))
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp π (fun t ↦ P (r t) (c (π.symm t))))

/-- Each rook placement has exactly k! ordered iid representations. -/
theorem sum_paired_embeddings_eq_factorial_rook {m n k : ℕ} (P : Board m n) :
    (∑ q : (Fin k ↪ Fin m) × (Fin k ↪ Fin n), ∏ t, P (q.1 t) (q.2 t)) =
      (k.factorial : ℝ) * rookSum P k := by
  rw [Fintype.sum_prod_type, ← (orderedEmbeddingPermEquiv m k).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ r : Fin k ↪o Fin m, ∑ π : Equiv.Perm (Fin k),
    ∑ c : Fin k ↪ Fin n, ∏ t, P (r (π t)) (c t)) = _
  simp_rw [sum_column_embeddings_permuted]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rfl

/-- General-order separation as the three weighted injection sums. -/
theorem separationProbability_eq_embedding_sums {m n : ℕ} (P : Board m n) (k : ℕ) :
    separationProbability P k =
      (∑ r : Fin k ↪ Fin m, ∏ t, rowSum P (r t)) +
      (∑ c : Fin k ↪ Fin n, ∏ t, colSum P (c t)) -
      ∑ q : (Fin k ↪ Fin m) × (Fin k ↪ Fin n), ∏ t, P (q.1 t) (q.2 t) := by
  change eventMass _ ({s | RowsDistinct s} ∪ {s | ColsDistinct s}) = _
  rw [eventMass_union]
  change _ + _ - eventMass _ {s | RowsDistinct s ∧ ColsDistinct s} = _
  rw [eventMass_rows_eq_sum_embeddings, eventMass_cols_eq_sum_embeddings,
    eventMass_rows_cols_eq_sum_embeddings]

/-- The rook-polynomial form of Rybin's inclusive-OR probability.

This is an exact polynomial identity on arbitrary real boards, including
every zero entry and every sample order. It is not an optimization claim.
-/
theorem separationProbability_eq_rook {m n : ℕ} (P : Board m n) (k : ℕ) :
    separationProbability P k = (k.factorial : ℝ) *
      (elementarySymmetric (rowSum P) k + elementarySymmetric (colSum P) k - rookSum P k) := by
  rw [separationProbability_eq_embedding_sums, sum_embeddings_eq_factorial_elementary,
    sum_embeddings_eq_factorial_elementary, sum_paired_embeddings_eq_factorial_rook]
  ring

theorem eventMass_rows_eq_factorial_elementary {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s} =
      (k.factorial : ℝ) * elementarySymmetric (rowSum P) k := by
  rw [eventMass_rows_eq_sum_embeddings, sum_embeddings_eq_factorial_elementary]

theorem eventMass_cols_eq_factorial_elementary {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | ColsDistinct s} =
      (k.factorial : ℝ) * elementarySymmetric (colSum P) k := by
  rw [eventMass_cols_eq_sum_embeddings, sum_embeddings_eq_factorial_elementary]

theorem eventMass_rows_cols_eq_factorial_rook {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s} =
      (k.factorial : ℝ) * rookSum P k := by
  rw [eventMass_rows_cols_eq_sum_embeddings, sum_paired_embeddings_eq_factorial_rook]

/-- Delete a set of rows by giving their cells zero weight, retaining the ambient index type. -/
def eraseRows {m n : ℕ} (P : Board m n) (S : Finset (Fin m)) : Board m n :=
  fun i j ↦ if i ∈ S then 0 else P i j

open Classical in
theorem sampleMass_eraseRows {m n k : ℕ} (P : Board m n) (S : Finset (Fin m))
    (s : Fin k → Fin m × Fin n) :
    sampleMass (fun a : Fin m × Fin n ↦ eraseRows P S a.1 a.2) s =
      if ∀ t, (s t).1 ∉ S then sampleMass (fun a : Fin m × Fin n ↦ P a.1 a.2) s else 0 := by
  unfold sampleMass
  have hterm (t : Fin k) : eraseRows P S (s t).1 (s t).2 =
      if (s t).1 ∉ S then P (s t).1 (s t).2 else 0 := by
    by_cases h : (s t).1 ∈ S <;> simp [eraseRows, h]
  simp_rw [hterm]
  have hprod := Fintype.prod_ite_zero (p := fun t : Fin k ↦ (s t).1 ∉ S)
    (f := fun t ↦ P (s t).1 (s t).2)
  by_cases hS : ∀ t, (s t).1 ∉ S <;> simpa only [hS, if_true, if_false] using hprod

/-- Row deletion is exactly restriction to samples avoiding those rows. -/
theorem eventMass_eraseRows {m n k : ℕ} (P : Board m n) (S : Finset (Fin m))
    (E : Set (Fin k → Fin m × Fin n)) :
    eventMass (fun a : Fin m × Fin n ↦ eraseRows P S a.1 a.2) E =
      eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2) {s | s ∈ E ∧ ∀ t, (s t).1 ∉ S} := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  rw [sampleMass_eraseRows]
  by_cases hE : s ∈ E <;> by_cases hS : ∀ t, (s t).1 ∉ S <;> simp [hE, hS]

/-- The excluded-row rook sum counts the actual joint separation-and-avoidance event. -/
theorem eventMass_avoid_rows_eq_factorial_rook {m n k : ℕ} (P : Board m n)
    (S : Finset (Fin m)) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s ∧ ∀ t, (s t).1 ∉ S} =
      (k.factorial : ℝ) * rookSum (eraseRows P S) k := by
  have h := eventMass_rows_cols_eq_factorial_rook (k := k) (eraseRows P S)
  rw [eventMass_eraseRows] at h
  simpa only [Set.mem_ofPred_eq, and_assoc] using h

end DittertRybin
