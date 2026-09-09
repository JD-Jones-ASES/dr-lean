import DR.Uniform
import DR.Square.Permanent
import Mathlib.Data.Fintype.EquivFin

/-!
# The square endpoint is Dittert's polynomial

The weighted counting identities below use ordered samples with replacement.
They are polynomial identities for arbitrary real matrices, without positivity
or normalization assumptions. At the square endpoint, a row or column
injection is a permutation, yielding the factorial factor in the reduction.
-/

namespace DittertRybin

open scoped BigOperators

/-- An event mass can equivalently be summed over the event's subtype. -/
theorem eventMass_eq_sum_subtype {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (E : Set (Fin k → α)) [Fintype E] :
    eventMass p E = ∑ s : E, sampleMass p s.val := by
  classical
  rw [eventMass, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Summing over column choices leaves the product of the selected row masses. -/
theorem eventMass_rows_eq_sum_embeddings {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s} =
        ∑ e : Fin k ↪ Fin m, ∏ t, rowSum P (e t) := by
  classical
  rw [eventMass_eq_sum_subtype]
  calc
    _ = ∑ q : (Fin k ↪ Fin m) × (Fin k → Fin n), ∏ t, P (q.1 t) (q.2 t) := by
      apply Fintype.sum_equiv (rowsDistinctEquiv m n k)
      intro s
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e _
      exact (Fintype.prod_sum fun t j => P (e t) j).symm

/-- Summing over row choices leaves the product of the selected column masses. -/
theorem eventMass_cols_eq_sum_embeddings {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | ColsDistinct s} =
        ∑ e : Fin k ↪ Fin n, ∏ t, colSum P (e t) := by
  classical
  rw [eventMass_eq_sum_subtype]
  calc
    _ = ∑ q : (Fin k → Fin m) × (Fin k ↪ Fin n), ∏ t, P (q.1 t) (q.2 t) := by
      apply Fintype.sum_equiv (colsDistinctEquiv m n k)
      intro s
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      exact (Fintype.prod_sum fun t i => P i (e t)).symm

/-- The intersection counts weighted pairs of row and column injections. -/
theorem eventMass_rows_cols_eq_sum_embeddings {m n k : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s} =
        ∑ q : (Fin k ↪ Fin m) × (Fin k ↪ Fin n), ∏ t, P (q.1 t) (q.2 t) := by
  classical
  rw [eventMass_eq_sum_subtype]
  apply Fintype.sum_equiv (rowsColsDistinctEquiv m n k)
  intro s
  rfl

/-- A product over a self-embedding uses every label exactly once. -/
theorem prod_comp_self_embedding {n : ℕ} (f : Fin n → ℝ) (e : Fin n ↪ Fin n) :
    (∏ t, f (e t)) = ∏ t, f t :=
  Equiv.prod_comp e.equivOfFiniteSelfEmbedding f

theorem eventMass_endpoint_rows {n : ℕ} (P : Board n n) :
    eventMass (fun a : Fin n × Fin n => P a.1 a.2)
      {s : Fin n → Fin n × Fin n | RowsDistinct s} =
        (n.factorial : ℝ) * ∏ i, rowSum P i := by
  classical
  rw [eventMass_rows_eq_sum_embeddings]
  simp [prod_comp_self_embedding, Fintype.card_embedding_eq, Nat.descFactorial_self,
    nsmul_eq_mul]

theorem eventMass_endpoint_cols {n : ℕ} (P : Board n n) :
    eventMass (fun a : Fin n × Fin n => P a.1 a.2)
      {s : Fin n → Fin n × Fin n | ColsDistinct s} =
        (n.factorial : ℝ) * ∏ j, colSum P j := by
  classical
  rw [eventMass_cols_eq_sum_embeddings]
  simp [prod_comp_self_embedding, Fintype.card_embedding_eq, Nat.descFactorial_self,
    nsmul_eq_mul]

theorem eventMass_endpoint_rows_cols {n : ℕ} (P : Board n n) :
    eventMass (fun a : Fin n × Fin n => P a.1 a.2)
      {s : Fin n → Fin n × Fin n | RowsDistinct s ∧ ColsDistinct s} =
        (n.factorial : ℝ) * P.permanent := by
  classical
  rw [eventMass_rows_cols_eq_sum_embeddings]
  calc
    _ = ∑ q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n), ∏ t, P (q.1 t) (q.2 t) := by
      apply Fintype.sum_equiv (Equiv.prodCongr
        (Equiv.embeddingEquivOfFinite (Fin n)) (Equiv.embeddingEquivOfFinite (Fin n)))
      intro q
      rfl
    _ = ∑ _τ : Equiv.Perm (Fin n), P.permanent := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      exact Matrix.permanent_permute_rows τ P
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

/-- Rybin's square endpoint is n! times the unscaled Dittert polynomial. -/
theorem separationProbability_endpoint {n : ℕ} (P : Board n n) :
    separationProbability P n =
      (n.factorial : ℝ) * ((∏ i, rowSum P i) + (∏ j, colSum P j) - P.permanent) := by
  change eventMass _ ({s | RowsDistinct s} ∪ {s | ColsDistinct s}) = _
  rw [eventMass_union]
  change _ + _ - eventMass _ {s | RowsDistinct s ∧ ColsDistinct s} = _
  rw [eventMass_endpoint_rows, eventMass_endpoint_cols, eventMass_endpoint_rows_cols]
  ring

/-- Dittert's functional is homogeneous of degree n. -/
theorem dittertFunctional_smul {n : ℕ} (P : Board n n) (c : ℝ) :
    dittertFunctional (c • P) = c ^ n * dittertFunctional P := by
  have hr (i : Fin n) : rowSum (c • P) i = c * rowSum P i := by
    simp [rowSum, Finset.mul_sum]
  have hc (j : Fin n) : colSum (c • P) j = c * colSum P j := by
    simp [colSum, Finset.mul_sum]
  simp only [dittertFunctional, hr, hc, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Matrix.permanent_smul]
  ring

/-- Under A=nP, the endpoint probability is (n!/n^n) times Dittert's functional. -/
theorem separationProbability_eq_dittert {n : ℕ} (hn : 0 < n) (P : Board n n) :
    separationProbability P n = dittertConstant n * dittertFunctional ((n : ℝ) • P) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [separationProbability_endpoint, dittertFunctional_smul]
  change (n.factorial : ℝ) * dittertFunctional P =
    dittertConstant n * ((n : ℝ) ^ n * dittertFunctional P)
  simp [dittertConstant, div_eq_mul_inv, ← mul_assoc, hn0]

end DittertRybin
