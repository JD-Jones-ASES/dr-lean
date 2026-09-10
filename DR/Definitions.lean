import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Matrices and the Dittert functional

The public statements use ordinary real matrices. The probability domain
allows zero entries and imposes only nonnegativity and total mass one.
-/

open scoped BigOperators

namespace DittertRybin

/-- A rectangular array of real cell weights. -/
abbrev Board (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Sum of the entries of one row. -/
def rowSum {m n : ℕ} (P : Board m n) (i : Fin m) : ℝ := ∑ j, P i j

/-- Sum of the entries of one column. -/
def colSum {m n : ℕ} (P : Board m n) (j : Fin n) : ℝ := ∑ i, P i j

/-- Total mass, summed first within each row. -/
def totalMass {m n : ℕ} (P : Board m n) : ℝ := ∑ i, rowSum P i

/-- The full closed probability simplex, including every boundary support. -/
def IsProbability {m n : ℕ} (P : Board m n) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ totalMass P = 1

/-- The uniform cell distribution. Its probability interpretation needs m,n>0. -/
noncomputable def uniformBoard (m n : ℕ) : Board m n := fun _ _ => ((m : ℝ) * n)⁻¹

/-- Dittert's polynomial on square matrices, usually with total mass n. -/
def dittertFunctional {n : ℕ} (A : Board n n) : ℝ :=
  (∏ i, rowSum A i) + (∏ j, colSum A j) - A.permanent

/-- The sharp permanent constant n!/n^n. -/
noncomputable def dittertConstant (n : ℕ) : ℝ := (n.factorial : ℝ) / (n : ℝ) ^ n

/-- The constant matrix of total mass n in Dittert's normalization. -/
noncomputable def uniformDittertMatrix (n : ℕ) : Board n n :=
  fun _ _ => (n : ℝ)⁻¹

/-- Dittert's sharp inequality and exact equality case on the full mass-n simplex. -/
def DittertMaximizer (n : ℕ) : Prop :=
  ∀ A : Board n n, (∀ i j, 0 ≤ A i j) → totalMass A = n →
    dittertFunctional A ≤ 2 - dittertConstant n ∧
    (dittertFunctional A = 2 - dittertConstant n ↔ A = uniformDittertMatrix n)

/-- Pair-collision count used in the all-order dimension threshold. -/
def collisionConstant (k : ℕ) : ℕ :=
  k.choose 2 * ((k.choose 2) ^ 2).choose 2

/-- A sufficient dimension threshold for the collision-kernel averaging bound. -/
def largeBoardThreshold (k : ℕ) : ℕ :=
  128 * (k - 2) * (collisionConstant k + 1) ^ 2

theorem totalMass_eq_sum_colSum {m n : ℕ} (P : Board m n) :
    totalMass P = ∑ j, colSum P j := by
  exact Finset.sum_comm

theorem rowSum_nonneg {m n : ℕ} {P : Board m n}
    (h : ∀ i j, 0 ≤ P i j) (i : Fin m) : 0 ≤ rowSum P i :=
  Finset.sum_nonneg fun j _ => h i j

theorem colSum_nonneg {m n : ℕ} {P : Board m n}
    (h : ∀ i j, 0 ≤ P i j) (j : Fin n) : 0 ≤ colSum P j :=
  Finset.sum_nonneg fun i _ => h i j

theorem uniformBoard_isProbability {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsProbability (uniformBoard m n) := by
  constructor
  · intro i j
    exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    simp only [totalMass, rowSum, uniformBoard, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem largeBoardThreshold_four : largeBoardThreshold 4 = 3659766016 := by decide

end DittertRybin
