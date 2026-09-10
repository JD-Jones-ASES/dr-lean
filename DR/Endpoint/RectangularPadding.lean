import DR.Endpoint.RectangularPaddingCounting
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-! The actual square padding of an m×n endpoint board. Original rows are
scaled by m and dummy rows are constant1/n. All algebra retains signed inputs;
positivity and balanced marginals are used only for doubly stochasticity. -/
namespace DittertRybin
open scoped BigOperators

/-- Square padding, with original rows first and constant dummy rows last. -/
noncomputable def rectangularPadding {m n : ℕ} (hmn : m ≤ n) (B : Board m n) : Board n n :=
  fun i j => Sum.elim (fun a => (m : ℝ) * B a j) (fun _ => 1/(n : ℝ))
    ((rectangularPaddingRowEquiv hmn).symm i)

@[simp] theorem rectangularPadding_original {m n : ℕ} (hmn : m ≤ n)
    (B : Board m n) (i : Fin m) (j : Fin n) :
    rectangularPadding hmn B (Fin.castLE hmn i) j = (m : ℝ) * B i j := by
  unfold rectangularPadding
  rw [← rectangularPaddingRowEquiv_inl hmn i]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem rectangularPadding_dummy {m n : ℕ} (hmn : m ≤ n)
    (B : Board m n) (i : Fin (n-m)) (j : Fin n) :
    rectangularPadding hmn B (rectangularPaddingRowEquiv hmn (.inr i)) j = 1/(n : ℝ) := by
  simp [rectangularPadding]

/-- Padding preserves every zero in an original row. -/
theorem rectangularPadding_zero {m n : ℕ} (hmn : m ≤ n)
    (B : Board m n) (i : Fin m) (j : Fin n) (hz : B i j = 0) :
    rectangularPadding hmn B (Fin.castLE hmn i) j = 0 := by
  simp [hz]

/-- No dummy rows means exactly scalar multiplication of the square input. -/
theorem rectangularPadding_square {n : ℕ} (B : Board n n) :
    rectangularPadding (le_refl n) B = (n : ℝ) • B := by
  ext i j
  simpa using rectangularPadding_original (le_refl n) B i j

/-- Entrywise nonnegativity is preserved even at zero dimensions. -/
theorem rectangularPadding_nonneg {m n : ℕ} (hmn : m ≤ n) (B : Board m n)
    (hB : ∀ i j, 0 ≤ B i j) : ∀ i j, 0 ≤ rectangularPadding hmn B i j := by
  intro i j
  obtain ⟨a, rfl⟩ := (rectangularPaddingRowEquiv hmn).surjective i
  cases a with
  | inl a => simpa using mul_nonneg (Nat.cast_nonneg m) (hB a j)
  | inr a => simp only [rectangularPadding_dummy]; positivity

/-- The same original cell witnesses a boundary point of the padded square. -/
theorem rectangularPadding_hasZero {m n : ℕ} (hmn : m ≤ n) (B : Board m n)
    (hz : ∃ i j, B i j = 0) : ∃ i j, rectangularPadding hmn B i j = 0 := by
  obtain ⟨i,j,hz⟩ := hz
  exact ⟨Fin.castLE hmn i,j,rectangularPadding_zero hmn B i j hz⟩

/-- Exact permanent identity with the dummy-row factorial. No sign or
normalization hypothesis is needed, and either row part may be empty. -/
theorem permanent_rectangularPadding {m n : ℕ} (hmn : m ≤ n) (B : Board m n) :
    (rectangularPadding hmn B).permanent =
      ((n-m).factorial : ℝ) * (m : ℝ)^m / (n : ℝ)^(n-m) * rookSum B m := by
  classical
  rw [← rowAvoidance_square_eq_permanent]
  let E := Equiv.embeddingCongr (rectangularPaddingRowEquiv hmn).symm (Equiv.refl (Fin n))
  have he : rowAvoidance (rectangularPadding hmn B) =
      ∑ z : Fin m ⊕ Fin (n-m) ↪ Fin n,
        (∏ i, (m : ℝ) * B i (z (.inl i))) * (1/(n : ℝ))^(n-m) := by
    unfold rowAvoidance rowAssignmentMass
    apply Fintype.sum_equiv E
    intro z
    change (∏ i, rectangularPadding hmn B i (z i)) =
      (∏ i, (m : ℝ) * B i (z (rectangularPaddingRowEquiv hmn (.inl i)))) * _
    rw [← Equiv.prod_comp (rectangularPaddingRowEquiv hmn)
      (fun i => rectangularPadding hmn B i (z i)), Fintype.prod_sum_type]
    simp only [rectangularPaddingRowEquiv_inl, rectangularPadding_original,
      rectangularPadding_dummy, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs := sum_embedding_with_constant_rows (α := Fin m) (β := Fin (n-m))
    (γ := Fin n) (by simp; omega) (fun i j => (m : ℝ) * B i j) (1/(n : ℝ))
  simp only [Fintype.card_fin] at hs
  rw [he, hs]
  simp only [Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum, rookSum_endpoint_eq_rowAvoidance]
  simp only [rowAvoidance, rowAssignmentMass, one_div_pow]
  ring

/-- Balanced rectangular marginals become unit square marginals after padding. -/
theorem rectangularPadding_mem_doublyStochastic {m n : ℕ} (hmn : m ≤ n)
    (hm : 0 < m) (hn : 0 < n) (B : Board m n)
    (hB : ∀ i j, 0 ≤ B i j)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ)) :
    rectangularPadding hmn B ∈ doublyStochastic ℝ (Fin n) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · exact rectangularPadding_nonneg hmn B hB
  · intro i
    obtain ⟨a, rfl⟩ := (rectangularPaddingRowEquiv hmn).surjective i
    cases a with
    | inl a =>
      simp only [rectangularPaddingRowEquiv_inl, rectangularPadding_original,
        ← Finset.mul_sum]
      rw [show (∑ j, B a j) = 1/(m : ℝ) from hr a]
      field_simp
    | inr a => simp [hn0]
  · intro j
    rw [← Equiv.sum_comp (rectangularPaddingRowEquiv hmn)
      (fun i => rectangularPadding hmn B i j), Fintype.sum_sum_type]
    simp only [rectangularPaddingRowEquiv_inl, rectangularPadding_original,
      rectangularPadding_dummy, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [show (∑ i, B i j) = 1/(n : ℝ) from hc j, Nat.cast_sub hmn]
    field_simp
    ring

/-- Uniform rectangular input produces the uniform doubly stochastic square. -/
theorem rectangularPadding_uniform {m n : ℕ} (hmn : m ≤ n) :
    rectangularPadding hmn (uniformBoard m n) = uniformDittertMatrix n := by
  ext i j
  obtain ⟨a, rfl⟩ := (rectangularPaddingRowEquiv hmn).surjective i
  cases a with
  | inl a =>
    have hm : 0 < m := by have := a.isLt; omega
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    rw [rectangularPaddingRowEquiv_inl, rectangularPadding_original]
    simp only [uniformBoard, uniformDittertMatrix]
    field_simp
  | inr a => simp [uniformDittertMatrix, one_div]

end DittertRybin
