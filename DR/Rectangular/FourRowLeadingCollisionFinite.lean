import DR.Rectangular.FourRowContenderInitial
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite four-sample identities for the leading collision term

Tuple expansions and marginalization are exact on arbitrary real weights.
The finite row identity counts the two orders of the complementary rows.
-/

namespace DittertRybin

open scoped BigOperators
open Classical

def fourRowSamplesFourEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun s := (s 0, s 1, s 2, s 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem fourRow_sum_samples_four {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  rw [← (fourRowSamplesFourEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

theorem fourRow_injective_four_iff {α : Type*} (s : Fin 4 → α) :
    Function.Injective s ↔ s 0 ≠ s 1 ∧ s 0 ≠ s 2 ∧ s 0 ≠ s 3 ∧
      s 1 ≠ s 2 ∧ s 1 ≠ s 3 ∧ s 2 ≠ s 3 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide), h.ne (by decide), h.ne (by decide),
      h.ne (by decide), h.ne (by decide), h.ne (by decide)⟩
  · rintro ⟨h01,h02,h03,h12,h13,h23⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Summing row outcomes yields the exact column sampling law for any observable. -/
theorem fourRow_column_observable {m n k : ℕ} (P : Board m n) (f : (Fin k → Fin n) → ℝ) :
    (∑ s : Fin k → Fin m × Fin n, sampleMass (fun a => P a.1 a.2) s * f (fun t => (s t).2)) =
      ∑ c, sampleMass (colSum P) c * f c := by
  calc
    _ = ∑ q : (Fin k → Fin m) × (Fin k → Fin n), (∏ t, P (q.1 t) (q.2 t)) * f q.2 := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin m) (fun _ => Fin n))
      intro s
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [← Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      congr 1
      exact (Fintype.prod_sum (fun t i => P i (c t))).symm

theorem fourRow_eventMass_columns {m n k : ℕ} (P : Board m n)
    (E : Set (Fin k → Fin n)) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2) {s | (fun t => (s t).2) ∈ E} =
      eventMass (colSum P) E := by
  simpa only [eventMass, mul_ite, mul_one, mul_zero, Set.mem_ofPred_eq] using
    fourRow_column_observable P (fun c => if c ∈ E then 1 else 0)

/-- In a fixed row assignment, two equal columns leave two free row masses. -/
theorem fourRow_fixed_rows_equal_columns {n : ℕ} (P : Board 4 n) (r : Fin 4 → Fin 4) :
    (∑ c : Fin 4 → Fin n, if c 0 = c 1 then ∏ t, P (r t) (c t) else 0) =
      (∑ j, P (r 0) j * P (r 1) j) * rowSum P (r 2) * rowSum P (r 3) := by
  rw [fourRow_sum_samples_four]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have ht (a b c d : Fin n) :
      (if a = b then P (r 0) a * P (r 1) b * P (r 2) c * P (r 3) d else 0) =
        (if a = b then P (r 0) a * P (r 1) b else 0) * P (r 2) c * P (r 3) d := by
    by_cases h : a = b <;> simp [h]
  simp_rw [ht, ← Finset.mul_sum]
  simp [← Finset.sum_mul, rowSum]
  exact Or.inl (by simp only [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_comm)

/-- The two complementary row orders give the exact off-diagonal factor two. -/
theorem fourRow_injective_pair_sum (r x : Fin 4 → ℝ) :
    (∑ s : Fin 4 → Fin 4, if Function.Injective s then
      x (s 0) * x (s 1) * r (s 2) * r (s 3) else 0) =
      2 * ∑ i, ∑ h, x i * fourRowColumnComplement r i h * x h := by
  rw [fourRow_sum_samples_four]
  simp only [fourRow_injective_four_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [Fin.sum_univ_four]
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  norm_num [fourRowColumnComplement, hu, Finset.prod_insert, Finset.erase_insert,
    Finset.erase_insert_of_ne, Finset.erase_singleton, Fin.ext_iff]
  ring

end DittertRybin
