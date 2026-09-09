import DR.Rook
import DR.Collision.Occupation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact two-column averaging of the iid semimatching probability

The combinatorial coefficient `E` is the elementary symmetric sum of the
remaining column masses. The matching-exclusion matrix has zero diagonal;
off diagonal it counts rook placements avoiding the two indicated rows.
The exact factorial counting identities identify `(E J - B)/E` with the
conditional occupation kernel, including its required diagonal correction.
An exact unique-label partition proves the column-deletion recurrences.
Applying these twice gives the full two-column expansion and the blend
identity for the actual iid functional on arbitrary real boards.
-/

namespace DittertRybin

open scoped BigOperators

/-- The elementary symmetric coefficient on the columns that remain after deletion. -/
noncomputable def averagingCoefficient {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  elementarySymmetric (colSum P) k

/-- Off-diagonal matching counts avoiding two rows; the diagonal is zero. -/
noncomputable def matchingExclusionKernel {m n : ℕ} (P : Board m n) (k : ℕ) :
    Matrix (Fin m) (Fin m) ℝ := fun i h ↦
  if i = h then 0 else rookSum (eraseRows P {i, h}) k

/-- The unnormalized quadratic kernel `G = E J - B`. -/
noncomputable def averagingKernel {m n : ℕ} (P : Board m n) (k : ℕ) :
    Matrix (Fin m) (Fin m) ℝ := fun i h ↦
  averagingCoefficient P k - matchingExclusionKernel P k i h

theorem columnDistinctMass_eq_factorial_coefficient {m n : ℕ} (P : Board m n) (k : ℕ) :
    columnDistinctMass P k = (k.factorial : ℝ) * averagingCoefficient P k :=
  eventMass_cols_eq_factorial_elementary P

theorem rows_absent_iff {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i h : Fin m) :
    (i ∉ occupiedRows s ∧ h ∉ occupiedRows s) ↔ ∀ t, (s t).1 ∉ ({i, h} : Finset (Fin m)) := by
  classical
  simp only [occupiedRows, Finset.mem_image, Finset.mem_univ, true_and,
    not_exists, Finset.mem_insert, Finset.mem_singleton, not_or, forall_and]

/-- The conditional avoidance probability is exactly the excluded-row rook ratio. -/
theorem conditionalRowsAbsent_eq_rook_ratio {m n : ℕ} (P : Board m n) (k : ℕ)
    (i h : Fin m) :
    conditionalRowsAbsent P k i h = rookSum (eraseRows P {i, h}) k / averagingCoefficient P k := by
  rw [conditionalRowsAbsent_eq_eventMass]
  have hevent : {s : Fin k → Fin m × Fin n | ColsDistinct s ∧ RowsDistinct s ∧
      i ∉ occupiedRows s ∧ h ∉ occupiedRows s} =
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∧ ColsDistinct s ∧
        ∀ t, (s t).1 ∉ ({i, h} : Finset (Fin m))} := by
    ext s
    simp only [Set.mem_ofPred_eq, ← rows_absent_iff]
    tauto
  rw [hevent, eventMass_avoid_rows_eq_factorial_rook, columnDistinctMass_eq_factorial_coefficient]
  exact mul_div_mul_left _ _ (by exact_mod_cast Nat.factorial_ne_zero k)

theorem averagingCoefficient_pos {m n : ℕ} (P : Board m n) (k : ℕ)
    (hZ : 0 < columnDistinctMass P k) : 0 < averagingCoefficient P k := by
  rw [columnDistinctMass_eq_factorial_coefficient] at hZ
  exact pos_of_mul_pos_right hZ (Nat.cast_nonneg _)

/-- Exact identification of the combinatorial averaging kernel and the conditional kernel. -/
theorem averagingKernel_eq_coefficient_occupationKernel {m n : ℕ} (P : Board m n) (k : ℕ)
    (hZ : 0 < columnDistinctMass P k) (i h : Fin m) :
    averagingKernel P k i h = averagingCoefficient P k * occupationKernel P k i h := by
  have hE := (averagingCoefficient_pos P k hZ).ne'
  by_cases hih : i = h
  · simp [averagingKernel, matchingExclusionKernel, occupationKernel, hih]
  · rw [averagingKernel, matchingExclusionKernel, if_neg hih, occupationKernel, if_neg hih,
      conditionalRowsAbsent_eq_rook_ratio]
    field_simp

/-- Mix two selected columns while preserving their entrywise sum. -/
def blendColumns {m n : ℕ} (P : Board m n) (a b : Fin n) (s : ℝ) : Board m n :=
  fun i j ↦ if j = a then (1 - s) * P i a + s * P i b
    else if j = b then s * P i a + (1 - s) * P i b else P i j

theorem blendColumns_eq_add_corrections {m n : ℕ} (P : Board m n)
    (a b : Fin n) (hab : a ≠ b) (s : ℝ) (i : Fin m) (j : Fin n) :
    blendColumns P a b s i j = P i j + (if j = a then s * (P i b - P i a) else 0) +
      (if j = b then s * (P i a - P i b) else 0) := by
  by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all [blendColumns] <;> ring

/-- Two-column blending leaves every row mass unchanged. -/
theorem rowSum_blendColumns {m n : ℕ} (P : Board m n) (a b : Fin n)
    (hab : a ≠ b) (s : ℝ) (i : Fin m) : rowSum (blendColumns P a b s) i = rowSum P i := by
  simp only [rowSum, blendColumns_eq_add_corrections P a b hab, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem blendColumns_nonneg {m n : ℕ} {P : Board m n} (hP : ∀ i j, 0 ≤ P i j)
    (a b : Fin n) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ i j, 0 ≤ blendColumns P a b s i j := by
  intro i j
  unfold blendColumns
  split_ifs
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (hP i a)) (mul_nonneg hs (hP i b))
  · exact add_nonneg (mul_nonneg hs (hP i a)) (mul_nonneg (sub_nonneg.mpr hs1) (hP i b))
  · exact hP i j

/-- Column blending stays in the full closed probability simplex. -/
theorem blendColumns_isProbability {m n : ℕ} {P : Board m n} (hP : IsProbability P)
    (a b : Fin n) (hab : a ≠ b) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsProbability (blendColumns P a b s) := by
  refine ⟨blendColumns_nonneg hP.1 a b s hs hs1, ?_⟩
  simpa only [totalMass, rowSum_blendColumns P a b hab] using hP.2

/-- The row term cancels exactly from the change in the actual iid functional. -/
theorem separationProbability_blend_difference {m n : ℕ} (P : Board m n)
    (a b : Fin n) (hab : a ≠ b) (s : ℝ) (k : ℕ) :
    separationProbability (blendColumns P a b s) k - separationProbability P k =
      (k.factorial : ℝ) *
        ((elementarySymmetric (colSum (blendColumns P a b s)) k -
          elementarySymmetric (colSum P) k) -
        (rookSum (blendColumns P a b s) k - rookSum P k)) := by
  have hr : rowSum (blendColumns P a b s) = rowSum P :=
    funext (rowSum_blendColumns P a b hab s)
  rw [separationProbability_eq_rook, separationProbability_eq_rook, hr]
  ring

theorem matchingExclusionKernel_symmetric {m n : ℕ} (P : Board m n) (k : ℕ)
    (i h : Fin m) : matchingExclusionKernel P k i h = matchingExclusionKernel P k h i := by
  by_cases hi : i = h
  · subst h
    rfl
  · simp [matchingExclusionKernel, hi, Ne.symm hi, Finset.pair_comm]

theorem averagingKernel_symmetric {m n : ℕ} (P : Board m n) (k : ℕ)
    (i h : Fin m) : averagingKernel P k i h = averagingKernel P k h i := by
  simp only [averagingKernel, matchingExclusionKernel_symmetric P k i h]

/-- The exact bilinear gain from blending two vectors in a symmetric kernel.
This is the algebraic step used after expanding the two selected columns.
-/
theorem bilinear_blend_difference {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ i j, H i j = H j i) (v w : Fin d → ℝ) (s : ℝ) :
    (∑ i, ∑ j, ((1 - s) * v i + s * w i) * H i j * (s * v j + (1 - s) * w j)) -
      (∑ i, ∑ j, v i * H i j * w j) =
        s * (1 - s) * ∑ i, ∑ j, (v i - w i) * H i j * (v j - w j) := by
  have hcross : (∑ i, ∑ j, w i * H i j * v j) = ∑ i, ∑ j, v i * H i j * w j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
    ring
  have hterm (i j : Fin d) :
      ((1 - s) * v i + s * w i) * H i j * (s * v j + (1 - s) * w j) =
        v i * H i j * w j + s * (1 - s) * ((v i - w i) * H i j * (v j - w j)) +
          s * (w i * H i j * v j - v i * H i j * w j) := by ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hcross]
  ring

/-- Delete selected columns without changing the ambient index type. -/
def eraseColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) : Board m n :=
  fun i j ↦ if j ∈ S then 0 else P i j

open Classical in
theorem sampleMass_eraseColumns {m n k : ℕ} (P : Board m n) (S : Finset (Fin n))
    (s : Fin k → Fin m × Fin n) :
    sampleMass (fun a : Fin m × Fin n ↦ eraseColumns P S a.1 a.2) s =
      if ∀ t, (s t).2 ∉ S then sampleMass (fun a : Fin m × Fin n ↦ P a.1 a.2) s else 0 := by
  unfold sampleMass
  have hterm (t : Fin k) : eraseColumns P S (s t).1 (s t).2 =
      if (s t).2 ∉ S then P (s t).1 (s t).2 else 0 := by
    by_cases h : (s t).2 ∈ S <;> simp [eraseColumns, h]
  simp_rw [hterm]
  have hprod := Fintype.prod_ite_zero (p := fun t : Fin k ↦ (s t).2 ∉ S)
    (f := fun t ↦ P (s t).1 (s t).2)
  by_cases hS : ∀ t, (s t).2 ∉ S <;> simpa only [hS, if_true, if_false] using hprod

theorem eventMass_eraseColumns {m n k : ℕ} (P : Board m n) (S : Finset (Fin n))
    (E : Set (Fin k → Fin m × Fin n)) :
    eventMass (fun a : Fin m × Fin n ↦ eraseColumns P S a.1 a.2) E =
      eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2) {s | s ∈ E ∧ ∀ t, (s t).2 ∉ S} := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  rw [sampleMass_eraseColumns]
  by_cases hE : s ∈ E <;> by_cases hS : ∀ t, (s t).2 ∉ S <;> simp [hE, hS]

theorem eventMass_permute {α : Type*} [Fintype α] {k : ℕ} (p : α → ℝ)
    (π : Equiv.Perm (Fin k)) (E : Set (Fin k → α)) :
    eventMass p {s | s ∘ π ∈ E} = eventMass p E := by
  classical
  unfold eventMass
  apply Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl α))
  intro s
  change (if s ∘ π ∈ E then sampleMass p s else 0) =
    if s ∘ π ∈ E then sampleMass p (s ∘ π) else 0
  congr 1
  exact (Equiv.prod_comp π (fun t ↦ p (s t))).symm

/-- Separate a label-distinct event according to the unique location of a selected label. -/
theorem eventMass_injectiveLabel_partition {α β : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (g : α → β) (a : β) (E : Set (Fin k → α))
    (hE : ∀ s ∈ E, Function.Injective (g ∘ s)) :
    eventMass p E = eventMass p {s | s ∈ E ∧ ∀ t, g (s t) ≠ a} +
      ∑ t, eventMass p {s | s ∈ E ∧ g (s t) = a} := by
  classical
  unfold eventMass
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ E
  · simp only [Set.mem_ofPred_eq, hs, true_and, if_true]
    by_cases hex : ∃ t, g (s t) = a
    · obtain ⟨t, ht⟩ := hex
      have hno : ¬∀ t, g (s t) ≠ a := by simpa only [not_forall, not_not] using ⟨t, ht⟩
      rw [if_neg hno, zero_add, Finset.sum_eq_single t]
      · simp [ht]
      · intro b _ hbt
        have hne : g (s b) ≠ a := fun hb ↦ hbt (hE s hs (hb.trans ht.symm))
        simp [hne]
      · simp
    · have hall : ∀ t, g (s t) ≠ a := not_exists.mp hex
      simp [hall]
  · simp [hs]

/-- Permutation symmetry turns the unique-label partition into an exact factor of the order. -/
theorem eventMass_injectiveLabel_split {α β : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (g : α → β) (a : β) (E : Set (Fin (k + 1) → α))
    (hE : ∀ s ∈ E, Function.Injective (g ∘ s))
    (hperm : ∀ (π : Equiv.Perm (Fin (k + 1))) s, s ∘ π ∈ E ↔ s ∈ E) :
    eventMass p E = eventMass p {s | s ∈ E ∧ ∀ t, g (s t) ≠ a} +
      (k + 1 : ℝ) * eventMass p {s | s ∈ E ∧ g (s 0) = a} := by
  classical
  rw [eventMass_injectiveLabel_partition p g a E hE]
  congr 1
  have ht (t : Fin (k + 1)) : eventMass p {s | s ∈ E ∧ g (s t) = a} =
      eventMass p {s | s ∈ E ∧ g (s 0) = a} := by
    have h := eventMass_permute p (Equiv.swap 0 t) {s | s ∈ E ∧ g (s 0) = a}
    simpa only [Set.mem_ofPred_eq, hperm, Function.comp_apply, Equiv.swap_apply_left] using h
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

/-- Split an ordered product-weight sample into its first cell and its tail. -/
theorem eventMass_head_tail {α : Type*} [Fintype α] {k : ℕ} (p : α → ℝ)
    (E : Set (Fin (k + 1) → α)) :
    eventMass p E = ∑ a, p a * eventMass p {s : Fin k → α | Fin.cons a s ∈ E} := by
  classical
  unfold eventMass
  calc
    _ = ∑ q : α × (Fin k → α), if Fin.cons q.1 q.2 ∈ E then
        p q.1 * sampleMass p q.2 else 0 := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ α))
      intro q
      change (if Fin.cons q.1 q.2 ∈ E then p q.1 * sampleMass p q.2 else 0) =
        if Fin.cons q.1 q.2 ∈ E then sampleMass p (Fin.cons q.1 q.2) else 0
      simp [sampleMass, Fin.prod_univ_succ]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      simp [Finset.mul_sum, mul_ite]

theorem rowsDistinct_permute {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (π : Equiv.Perm (Fin k)) : RowsDistinct (s ∘ π) ↔ RowsDistinct s :=
  π.injective_comp (fun t ↦ (s t).1)

theorem colsDistinct_permute {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (π : Equiv.Perm (Fin k)) : ColsDistinct (s ∘ π) ↔ ColsDistinct s :=
  π.injective_comp (fun t ↦ (s t).2)

theorem rowsDistinct_cons {m n k : ℕ} (x : Fin m × Fin n) (s : Fin k → Fin m × Fin n) :
    RowsDistinct (Fin.cons x s) ↔ RowsDistinct s ∧ ∀ t, (s t).1 ≠ x.1 := by
  change Function.Injective (Prod.fst ∘ Fin.cons x s) ↔ _
  rw [Fin.comp_cons, Fin.cons_injective_iff]
  simp [RowsDistinct, Set.mem_range, and_comm, Function.comp_def]

theorem colsDistinct_cons {m n k : ℕ} (x : Fin m × Fin n) (s : Fin k → Fin m × Fin n) :
    ColsDistinct (Fin.cons x s) ↔ ColsDistinct s ∧ ∀ t, (s t).2 ≠ x.2 := by
  change Function.Injective (Prod.snd ∘ Fin.cons x s) ↔ _
  rw [Fin.comp_cons, Fin.cons_injective_iff]
  simp [ColsDistinct, Set.mem_range, and_comm, Function.comp_def]

theorem eventMass_head_column {m n k : ℕ} (P : Board m n) (a : Fin n)
    (E : Set (Fin (k + 1) → Fin m × Fin n)) :
    eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2) {s | s ∈ E ∧ (s 0).2 = a} =
      ∑ i, P i a * eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
        {s : Fin k → Fin m × Fin n | Fin.cons (i, a) s ∈ E} := by
  classical
  rw [eventMass_head_tail, Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hterm (j : Fin n) :
      P i j * eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
          {s : Fin k → Fin m × Fin n | Fin.cons (i, j) s ∈ E ∧ j = a} =
        if j = a then P i a * eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
          {s : Fin k → Fin m × Fin n | Fin.cons (i, a) s ∈ E} else 0 := by
    by_cases hj : j = a <;> simp [hj, eventMass]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact one-column deletion recurrence for weighted rook sums. -/
theorem rookSum_column_deletion {m n k : ℕ} (P : Board m n) (a : Fin n) :
    rookSum P (k + 1) = rookSum (eraseColumns P {a}) (k + 1) +
      ∑ i, P i a * rookSum (eraseRows (eraseColumns P {a}) {i}) k := by
  classical
  let E : Set (Fin (k + 1) → Fin m × Fin n) := {s | RowsDistinct s ∧ ColsDistinct s}
  have h := eventMass_injectiveLabel_split (fun x : Fin m × Fin n ↦ P x.1 x.2)
    Prod.snd a E (fun s hs ↦ hs.2) (by
      intro π s
      exact and_congr (rowsDistinct_permute s π) (colsDistinct_permute s π))
  have havoid : eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
      {s | s ∈ E ∧ ∀ t, (s t).2 ≠ a} =
      ((k + 1).factorial : ℝ) * rookSum (eraseColumns P {a}) (k + 1) := by
    rw [← eventMass_rows_cols_eq_factorial_rook, eventMass_eraseColumns]
    simp only [E, Finset.mem_singleton]
  have htail (i : Fin m) : eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
      {s : Fin k → Fin m × Fin n | Fin.cons (i, a) s ∈ E} =
      (k.factorial : ℝ) * rookSum (eraseRows (eraseColumns P {a}) {i}) k := by
    rw [← eventMass_rows_cols_eq_factorial_rook, eventMass_eraseRows, eventMass_eraseColumns]
    congr 1
    ext s
    simp only [E, Set.mem_ofPred_eq, rowsDistinct_cons, colsDistinct_cons, Finset.mem_singleton]
    tauto
  change eventMass _ {s | RowsDistinct s ∧ ColsDistinct s} = _ at h
  rw [eventMass_rows_cols_eq_factorial_rook, havoid, eventMass_head_column] at h
  simp only [htail, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hsum : (∑ i, P i a * ((k.factorial : ℝ) *
      rookSum (eraseRows (eraseColumns P {a}) {i}) k)) =
      (k.factorial : ℝ) * ∑ i, P i a * rookSum (eraseRows (eraseColumns P {a}) {i}) k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at h
  have hfac : (k + 1 : ℝ) * (k.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hfac
  calc
    _ = _ := h
    _ = _ := by ring

/-- Exact one-column deletion recurrence for elementary column coefficients. -/
theorem elementary_column_deletion {m n k : ℕ} (P : Board m n) (a : Fin n) :
    elementarySymmetric (colSum P) (k + 1) =
      elementarySymmetric (colSum (eraseColumns P {a})) (k + 1) +
        colSum P a * elementarySymmetric (colSum (eraseColumns P {a})) k := by
  classical
  let E : Set (Fin (k + 1) → Fin m × Fin n) := {s | ColsDistinct s}
  have h := eventMass_injectiveLabel_split (fun x : Fin m × Fin n ↦ P x.1 x.2)
    Prod.snd a E (fun _ hs ↦ hs) (fun π s ↦ colsDistinct_permute s π)
  have havoid : eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
      {s | s ∈ E ∧ ∀ t, (s t).2 ≠ a} =
      ((k + 1).factorial : ℝ) *
        elementarySymmetric (colSum (eraseColumns P {a})) (k + 1) := by
    rw [← eventMass_cols_eq_factorial_elementary, eventMass_eraseColumns]
    simp only [E, Finset.mem_singleton]
  have htail (i : Fin m) : eventMass (fun x : Fin m × Fin n ↦ P x.1 x.2)
      {s : Fin k → Fin m × Fin n | Fin.cons (i, a) s ∈ E} =
      (k.factorial : ℝ) * elementarySymmetric (colSum (eraseColumns P {a})) k := by
    rw [← eventMass_cols_eq_factorial_elementary, eventMass_eraseColumns]
    congr 1
    ext s
    simp only [E, Set.mem_ofPred_eq, colsDistinct_cons, Finset.mem_singleton]
  change eventMass _ {s | ColsDistinct s} = _ at h
  rw [eventMass_cols_eq_factorial_elementary, havoid, eventMass_head_column] at h
  simp only [htail, ← Finset.sum_mul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hfac : (k + 1 : ℝ) * (k.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hfac
  calc
    _ = _ := h
    _ = _ := by unfold colSum; ring

theorem eraseColumns_eraseColumns {m n : ℕ} (P : Board m n) (S T : Finset (Fin n)) :
    eraseColumns (eraseColumns P S) T = eraseColumns P (S ∪ T) := by
  ext i j
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [eraseColumns, hS, hT]

theorem eraseRows_eraseRows {m n : ℕ} (P : Board m n) (S T : Finset (Fin m)) :
    eraseRows (eraseRows P S) T = eraseRows P (S ∪ T) := by
  ext i j
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [eraseRows, hS, hT]

theorem eraseColumns_eraseRows {m n : ℕ} (P : Board m n) (S : Finset (Fin m))
    (T : Finset (Fin n)) : eraseColumns (eraseRows P S) T = eraseRows (eraseColumns P T) S := by
  ext i j
  by_cases hS : i ∈ S <;> by_cases hT : j ∈ T <;> simp [eraseRows, eraseColumns, hS, hT]

theorem colSum_eraseColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) (j : Fin n) :
    colSum (eraseColumns P S) j = if j ∈ S then 0 else colSum P j := by
  by_cases hj : j ∈ S <;> simp [colSum, eraseColumns, hj]

/-- Expanding two selected columns counts the four possible occupation patterns exactly. -/
theorem rookSum_two_columns {m n k : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) :
    rookSum P (k + 2) = rookSum (eraseColumns P {a, b}) (k + 2) +
      (∑ i, (P i a + P i b) * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1)) +
      ∑ i, ∑ h, P i a * matchingExclusionKernel (eraseColumns P {a, b}) k i h * P h b := by
  classical
  have he (i : Fin m) :
      rookSum (eraseRows (eraseColumns P {a}) {i}) (k + 1) =
        rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1) +
          ∑ h, matchingExclusionKernel (eraseColumns P {a, b}) k i h * P h b := by
    rw [rookSum_column_deletion _ b]
    simp only [eraseColumns_eraseRows, eraseColumns_eraseColumns, Finset.singleton_union,
      eraseRows_eraseRows]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    by_cases hhi : h = i
    · subst h
      simp [eraseRows, matchingExclusionKernel]
    · simp [eraseRows, eraseColumns, Ne.symm hab, hhi, Ne.symm hhi,
        matchingExclusionKernel, mul_comm]
  rw [show k + 2 = (k + 1) + 1 by omega, rookSum_column_deletion P a,
    rookSum_column_deletion (eraseColumns P {a}) b]
  simp only [eraseColumns_eraseColumns, Finset.singleton_union, eraseColumns,
    Finset.mem_singleton, if_neg (Ne.symm hab), he, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  have hline : (∑ i, P i a * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1)) +
      (∑ i, P i b * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1)) =
      ∑ i, (P i a + P i b) * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hbil : (∑ i, ∑ h, P i a *
      (matchingExclusionKernel (eraseColumns P {a, b}) k i h * P h b)) =
      ∑ i, ∑ h, P i a * matchingExclusionKernel (eraseColumns P {a, b}) k i h * P h b := by
    simp only [mul_assoc]
  -- Keep the common residual board intact while combining the finite sums.
  change rookSum (eraseColumns P {a, b}) (k + 1 + 1) +
      (∑ i, P i b * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1)) +
      ((∑ i, P i a * rookSum (eraseRows (eraseColumns P {a, b}) {i}) (k + 1)) +
        (∑ i, ∑ h, P i a * (matchingExclusionKernel (eraseColumns P {a, b}) k i h * P h b))) = _
  rw [hbil]
  rw [← hline]
  ring

/-- The corresponding exact two-column expansion of the elementary coefficient. -/
theorem elementary_two_columns {m n k : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) :
    elementarySymmetric (colSum P) (k + 2) =
      elementarySymmetric (colSum (eraseColumns P {a, b})) (k + 2) +
      (colSum P a + colSum P b) * elementarySymmetric (colSum (eraseColumns P {a, b})) (k + 1) +
      colSum P a * averagingCoefficient (eraseColumns P {a, b}) k * colSum P b := by
  rw [show k + 2 = (k + 1) + 1 by omega, elementary_column_deletion P a,
    elementary_column_deletion (eraseColumns P {a}) b,
    elementary_column_deletion (eraseColumns P {a}) b]
  simp only [eraseColumns_eraseColumns, Finset.singleton_union, colSum_eraseColumns,
    Finset.mem_singleton, if_neg (Ne.symm hab), averagingCoefficient]
  ring

theorem eraseColumns_blendColumns {m n : ℕ} (P : Board m n) (a b : Fin n) (s : ℝ) :
    eraseColumns (blendColumns P a b s) {a, b} = eraseColumns P {a, b} := by
  ext i j
  by_cases ha : j = a <;> by_cases hb : j = b <;> simp [eraseColumns, blendColumns, ha, hb]

theorem blendColumns_left {m n : ℕ} (P : Board m n) (a b : Fin n) (s : ℝ) (i : Fin m) :
    blendColumns P a b s i a = (1 - s) * P i a + s * P i b := by
  simp [blendColumns]

theorem blendColumns_right {m n : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b)
    (s : ℝ) (i : Fin m) : blendColumns P a b s i b = s * P i a + (1 - s) * P i b := by
  simp [blendColumns, Ne.symm hab]

theorem colSum_blendColumns_left {m n : ℕ} (P : Board m n) (a b : Fin n) (s : ℝ) :
    colSum (blendColumns P a b s) a = (1 - s) * colSum P a + s * colSum P b := by
  simp [colSum, blendColumns_left, Finset.sum_add_distrib, Finset.mul_sum]

theorem colSum_blendColumns_right {m n : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) (s : ℝ) :
    colSum (blendColumns P a b s) b = s * colSum P a + (1 - s) * colSum P b := by
  simp [colSum, blendColumns_right P a b hab, Finset.sum_add_distrib, Finset.mul_sum]

theorem elementary_blend_difference {m n k : ℕ} (P : Board m n) (a b : Fin n)
    (hab : a ≠ b) (s : ℝ) :
    elementarySymmetric (colSum (blendColumns P a b s)) (k + 2) -
      elementarySymmetric (colSum P) (k + 2) =
      s * (1 - s) * (colSum P a - colSum P b) ^ 2 * averagingCoefficient (eraseColumns P {a, b}) k := by
  rw [elementary_two_columns (blendColumns P a b s) a b hab,
    elementary_two_columns P a b hab, eraseColumns_blendColumns,
    colSum_blendColumns_left, colSum_blendColumns_right P a b hab]
  ring

theorem rookSum_blend_difference {m n k : ℕ} (P : Board m n) (a b : Fin n)
    (hab : a ≠ b) (s : ℝ) :
    rookSum (blendColumns P a b s) (k + 2) - rookSum P (k + 2) =
      s * (1 - s) * ∑ i, ∑ h, (P i a - P i b) *
        matchingExclusionKernel (eraseColumns P {a, b}) k i h * (P h a - P h b) := by
  rw [rookSum_two_columns (blendColumns P a b s) a b hab,
    rookSum_two_columns P a b hab, eraseColumns_blendColumns]
  simp only [blendColumns_left, blendColumns_right P a b hab]
  have hline (i : Fin m) : ((1 - s) * P i a + s * P i b) +
      (s * P i a + (1 - s) * P i b) = P i a + P i b := by ring
  simp only [hline]
  have hbil := bilinear_blend_difference (matchingExclusionKernel (eraseColumns P {a, b}) k)
    (matchingExclusionKernel_symmetric (eraseColumns P {a, b}) k)
    (fun i ↦ P i a) (fun i ↦ P i b) s
  convert hbil using 1
  ring

theorem quadratic_averagingKernel {m n : ℕ} (P : Board m n) (k : ℕ) (x : Fin m → ℝ) :
    (∑ i, ∑ h, x i * averagingKernel P k i h * x h) =
      averagingCoefficient P k * (∑ i, x i) ^ 2 -
        ∑ i, ∑ h, x i * matchingExclusionKernel P k i h * x h := by
  simp only [averagingKernel, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The exact two-column blend identity for the actual iid semimatching functional.

The residual board deletes the selected columns. Its elementary coefficient and
zero-diagonal matching-exclusion matrix give the quadratic kernel. This identity
holds for signed boards and every blend parameter, with no optimization hypothesis.
-/
theorem separationProbability_blend_identity {m n k : ℕ} (P : Board m n)
    (a b : Fin n) (hab : a ≠ b) (s : ℝ) :
    separationProbability (blendColumns P a b s) (k + 2) - separationProbability P (k + 2) =
      s * (1 - s) * ((k + 2).factorial : ℝ) *
        ∑ i, ∑ h, (P i a - P i b) * averagingKernel (eraseColumns P {a, b}) k i h *
          (P h a - P h b) := by
  rw [separationProbability_blend_difference P a b hab, elementary_blend_difference P a b hab,
    rookSum_blend_difference P a b hab, quadratic_averagingKernel]
  have hsum : (∑ i, (P i a - P i b)) = colSum P a - colSum P b := by
    simp only [colSum, Finset.sum_sub_distrib]
  rw [hsum]
  ring

theorem separationProbability_blend_identity_of_two_le {m n k : ℕ} (P : Board m n)
    (hk : 2 ≤ k) (a b : Fin n) (hab : a ≠ b) (s : ℝ) :
    separationProbability (blendColumns P a b s) k - separationProbability P k =
      s * (1 - s) * (k.factorial : ℝ) *
        ∑ i, ∑ h, (P i a - P i b) * averagingKernel (eraseColumns P {a, b}) (k - 2) i h *
          (P h a - P h b) := by
  simpa only [Nat.sub_add_cancel hk] using
    separationProbability_blend_identity (k := k - 2) P a b hab s

end DittertRybin
