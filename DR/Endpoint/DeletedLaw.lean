import DR.Endpoint.Contenders
import DR.Collision.Deletion

/-!
# The original and deleted independent-row laws

Deleting columns changes every affected row normalization. Its avoidance
probability is kept as a separate named quantity; no contender relation for
the original board is silently asserted for the deleted law. Common scaling
of the retained board does preserve that law, including zero row sums.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def deletedRowAvoidance {m n : ℕ} (P : Board m n) (a b : Fin n) : ℝ :=
  rowAvoidance (normalizeRows (keepColumns P ({a,b}ᶜ)))

theorem normalizeRows_smul {m n : ℕ} (P : Board m n) {c : ℝ} (hc : c ≠ 0) :
    normalizeRows (c • P) = normalizeRows P := by
  funext i j
  change (c*P i j)/(∑ j, c*P i j) = P i j/(∑ j, P i j)
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

theorem normalizeRows_normalizeBoard {m n : ℕ} (P : Board m n)
    (hμ : totalMass P ≠ 0) : normalizeRows (normalizeBoard P) = normalizeRows P := by
  funext i j
  simp only [normalizeRows,normalizeBoard,rowSum_normalizeBoard]
  exact div_div_div_cancel_right₀ hμ _ _

/-- Total-mass normalization of the retained board does not change its own row law. -/
theorem deletedRowAvoidance_eq_normalized_retained {m n : ℕ} (P : Board m n)
    (a b : Fin n) (hμ : totalMass (keepColumns P ({a,b}ᶜ)) ≠ 0) :
    deletedRowAvoidance P a b =
      originalRowAvoidance (normalizeBoard (keepColumns P ({a,b}ᶜ))) := by
  rw [originalRowAvoidance,normalizeRows_normalizeBoard _ hμ]
  rfl

/-- A probability interpretation requires positive retained row sums, not merely positive mass. -/
theorem deletedRowAvoidance_bounds {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n)
    (hr : ∀ i, 0 < rowSum (keepColumns P ({a,b}ᶜ)) i) :
    0 ≤ deletedRowAvoidance P a b ∧ deletedRowAvoidance P a b ≤ 1 := by
  have hn := normalizeRows_nonneg (keepColumns P ({a,b}ᶜ)) (keepColumns_nonneg hP _)
  exact ⟨rowAvoidance_nonneg _ hn,rowAvoidance_le_one _ hn
    (normalizeRows_rowSum _ (fun i => (hr i).ne'))⟩

/-- The deleted rook normalization has its own product and its own avoidance factor. -/
theorem deleted_rook_normalization {m n : ℕ} (P : Board m n) (a b : Fin n)
    (hr : ∀ i, rowSum (keepColumns P ({a,b}ᶜ)) i ≠ 0) :
    rookSum (keepColumns P ({a,b}ᶜ)) m =
      (∏ i, rowSum (keepColumns P ({a,b}ᶜ)) i)*deletedRowAvoidance P a b :=
  rookSum_endpoint_normalized _ hr

end DittertRybin
