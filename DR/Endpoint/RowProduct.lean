import DR.Rook

/-!
# Independent, non-identically distributed row assignments

There is one column choice per row. Each row has its own distribution;
these are not iid draws from the cell probability matrix. The injection
event is the original-row collision-avoidance probability. Applying these
definitions to a deleted board gives a separate law and separate avoidance
probability, with its own row normalization.
-/

namespace DittertRybin
open scoped BigOperators

def rowAssignmentMass {m n : ℕ} (X : Board m n) (z : Fin m → Fin n) : ℝ :=
  ∏ i, X i (z i)

noncomputable def rowAssignmentEvent {m n : ℕ} (X : Board m n)
    (E : Set (Fin m → Fin n)) : ℝ := by
  classical
  exact ∑ z, if z ∈ E then rowAssignmentMass X z else 0

/-- Collision avoidance under one independent column choice in each row. -/
noncomputable def rowAvoidance {m n : ℕ} (X : Board m n) : ℝ :=
  ∑ e : Fin m ↪ Fin n, rowAssignmentMass X e

noncomputable def normalizeRows {m n : ℕ} (P : Board m n) : Board m n :=
  fun i j => P i j / rowSum P i

theorem sum_rowAssignmentMass {m n : ℕ} (X : Board m n) :
    (∑ z, rowAssignmentMass X z) = ∏ i, rowSum X i :=
  (Fintype.prod_sum fun i j => X i j).symm

theorem rowAssignmentMass_nonneg {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (z : Fin m → Fin n) :
    0 ≤ rowAssignmentMass X z :=
  Finset.prod_nonneg fun i _ => hX i (z i)

theorem rowAssignmentEvent_nonneg {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (E : Set (Fin m → Fin n)) :
    0 ≤ rowAssignmentEvent X E := by
  classical
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact rowAssignmentMass_nonneg X hX z
  · rfl

theorem rowAssignmentEvent_univ {m n : ℕ} (X : Board m n) :
    rowAssignmentEvent X Set.univ = ∏ i, rowSum X i := by
  simpa [rowAssignmentEvent] using sum_rowAssignmentMass X

theorem rowAssignmentEvent_le_total {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (E : Set (Fin m → Fin n)) :
    rowAssignmentEvent X E ≤ ∏ i, rowSum X i := by
  classical
  rw [← sum_rowAssignmentMass]
  apply Finset.sum_le_sum
  intro z hz
  split_ifs
  · rfl
  · exact rowAssignmentMass_nonneg X hX z

theorem rowAssignmentEvent_compl {m n : ℕ} (X : Board m n)
    (E : Set (Fin m → Fin n)) :
    rowAssignmentEvent X Eᶜ = (∏ i, rowSum X i) - rowAssignmentEvent X E := by
  classical
  have h : rowAssignmentEvent X E + rowAssignmentEvent X Eᶜ =
      ∑ z, rowAssignmentMass X z := by
    simp only [rowAssignmentEvent, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases he : z ∈ E <;> simp [he]
  rw [sum_rowAssignmentMass] at h
  linarith

theorem rowAssignmentEvent_eq_sum_subtype {m n : ℕ} (X : Board m n)
    (E : Set (Fin m → Fin n)) [Fintype E] :
    rowAssignmentEvent X E = ∑ z : E, rowAssignmentMass X z.val := by
  classical
  rw [rowAssignmentEvent, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem rowAvoidance_eq_event {m n : ℕ} (X : Board m n) :
    rowAvoidance X = rowAssignmentEvent X {z | Function.Injective z} := by
  classical
  let e : (Fin m ↪ Fin n) ≃ {z : Fin m → Fin n // Function.Injective z} :=
    { toFun := fun z => ⟨z,z.injective⟩
      invFun := fun z => ⟨z.val,z.property⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  rw [rowAssignmentEvent_eq_sum_subtype]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rowAvoidance_nonneg {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) : 0 ≤ rowAvoidance X := by
  rw [rowAvoidance_eq_event]
  exact rowAssignmentEvent_nonneg X hX _

theorem rowAvoidance_le_one {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hsum : ∀ i, rowSum X i = 1) :
    rowAvoidance X ≤ 1 := by
  rw [rowAvoidance_eq_event]
  simpa [hsum] using rowAssignmentEvent_le_total X hX {z | Function.Injective z}

theorem normalizeRows_nonneg {m n : ℕ} (P : Board m n)
    (hP : ∀ i j, 0 ≤ P i j) : ∀ i j, 0 ≤ normalizeRows P i j := by
  intro i j
  exact div_nonneg (hP i j) (Finset.sum_nonneg fun k hk => hP i k)

theorem normalizeRows_rowSum {m n : ℕ} (P : Board m n)
    (hr : ∀ i, rowSum P i ≠ 0) (i : Fin m) : rowSum (normalizeRows P) i = 1 := by
  simp only [rowSum, normalizeRows, ← Finset.sum_div]
  exact div_self (hr i)

theorem rowAssignmentMass_normalizeRows {m n : ℕ} (P : Board m n)
    (z : Fin m → Fin n) :
    rowAssignmentMass (normalizeRows P) z = rowAssignmentMass P z / ∏ i, rowSum P i := by
  simp only [rowAssignmentMass, normalizeRows, Finset.prod_div_distrib]

theorem rowAvoidance_normalizeRows {m n : ℕ} (P : Board m n) :
    rowAvoidance (normalizeRows P) = rowAvoidance P / ∏ i, rowSum P i := by
  simp only [rowAvoidance, rowAssignmentMass_normalizeRows, Finset.sum_div]

/-- The endpoint rook sum counts one row assignment, with no factorial. -/
theorem rookSum_endpoint_eq_rowAvoidance {m n : ℕ} (P : Board m n) :
    rookSum P m = rowAvoidance P := by
  classical
  have h := sum_paired_embeddings_eq_factorial_rook (k := m) P
  rw [Fintype.sum_prod_type] at h
  have hr (r : Fin m ↪ Fin m) :
      (∑ c : Fin m ↪ Fin n, ∏ t, P (r t) (c t)) = rowAvoidance P := by
    exact sum_column_embeddings_permuted P (fun i => i) r.equivOfFiniteSelfEmbedding
  simp_rw [hr] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, Nat.descFactorial_self, nsmul_eq_mul] at h
  exact (mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m) h).symm

/-- Recover the actual rook sum from the normalized original-row law. -/
theorem rookSum_endpoint_normalized {m n : ℕ} (P : Board m n)
    (hr : ∀ i, rowSum P i ≠ 0) :
    rookSum P m = (∏ i, rowSum P i) * rowAvoidance (normalizeRows P) := by
  rw [rookSum_endpoint_eq_rowAvoidance, rowAvoidance_normalizeRows]
  have hprod : (∏ i, rowSum P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => hr i
  field_simp


/-- On a square board, one independent row assignment gives the permanent,
without the factorial that belongs to ordered iid cell sampling. -/
theorem rowAvoidance_square_eq_permanent {n : ℕ} (P : Board n n) :
    rowAvoidance P = P.permanent := by
  have h := eventMass_rows_cols_eq_factorial_rook (k := n) P
  rw [eventMass_endpoint_rows_cols, rookSum_endpoint_eq_rowAvoidance] at h
  exact (mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n) h).symm

end DittertRybin
