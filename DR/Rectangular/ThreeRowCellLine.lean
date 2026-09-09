import DR.Rectangular.ThreeRowCubic

/-! Exact one-cell variation identities for the three-row cubic, including at zero cells. -/

namespace DittertRybin
open scoped BigOperators

/-- Add a signed amount to one physical cell. -/
def threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n) (t : ℝ) : Board 3 n :=
  fun i j => P i j + if i = a ∧ j = b then t else 0

theorem rowSum_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n)
    (t : ℝ) (i : Fin 3) : rowSum (threeRowAddCell P a b t) i = rowSum P i + if i = a then t else 0 := by
  simp [rowSum, threeRowAddCell, Finset.sum_add_distrib, ite_and]

theorem colSum_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n)
    (t : ℝ) (j : Fin n) : colSum (threeRowAddCell P a b t) j = colSum P j + if j = b then t else 0 := by
  simp [colSum, threeRowAddCell, Finset.sum_add_distrib, ite_and]

theorem totalMass_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n) (t : ℝ) :
    totalMass (threeRowAddCell P a b t) = totalMass P + t := by
  simp [totalMass, rowSum_threeRowAddCell, Finset.sum_add_distrib]

/-- Replacing one column mass changes every finite scalar sum at exactly that index. -/
theorem sum_colSum_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n)
    (t : ℝ) (f : ℝ → ℝ) :
    (∑ j, f (colSum (threeRowAddCell P a b t) j)) =
      (∑ j, f (colSum P j)) + f (colSum P b + t) - f (colSum P b) := by
  have hterm (j : Fin n) : f (colSum (threeRowAddCell P a b t) j) = f (colSum P j) +
      if j = b then f (colSum P b + t) - f (colSum P b) else 0 := by
    rw [colSum_threeRowAddCell]
    by_cases hj : j = b
    · subst j
      simp only [if_true]
      ring
    · simp only [if_neg hj, add_zero]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The complementary row pair changes linearly, even when its unchanged factor is zero. -/
theorem threeRowPair_addCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n)
    (t : ℝ) (i : Fin 3) :
    threeRowPair (threeRowAddCell P a b t) i = threeRowPair P i +
      (if i + 1 = a then t * P (i + 2) b else 0) +
      (if i + 2 = a then t * P (i + 1) b else 0) := by
  fin_cases i <;> fin_cases a <;>
    simp [threeRowPair, threeRowAddCell, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

/-- The contraction of row masses with complementary column pairs has no repeated-row term. -/
theorem sum_rowPair_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n) (t : ℝ) :
    (∑ i, rowSum (threeRowAddCell P a b t) i * threeRowPair (threeRowAddCell P a b t) i) =
      (∑ i, rowSum P i * threeRowPair P i) +
      t * (threeRowPair P a + rowSum P (a + 1) * P (a + 2) b +
        rowSum P (a + 2) * P (a + 1) b) := by
  simp_rw [rowSum_threeRowAddCell, threeRowPair_addCell]
  fin_cases a <;> simp [Fin.sum_univ_succ] <;> ring

/-- Retain the derivative of the full-column triple product at every boundary cell. -/
theorem sum_triple_threeRowAddCell {n : ℕ} (P : Board 3 n) (a : Fin 3) (b : Fin n) (t : ℝ) :
    (∑ j, threeRowAddCell P a b t 0 j * threeRowAddCell P a b t 1 j * threeRowAddCell P a b t 2 j) =
      (∑ j, P 0 j * P 1 j * P 2 j) + t * P (a + 1) b * P (a + 2) b := by
  fin_cases a <;> simp [threeRowAddCell, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

/-- The actual probability polynomial is affine in each physical cell, with the exact derivative. -/
theorem separationProbability_threeRow_addCell {n : ℕ} (P : Board 3 n)
    (a : Fin 3) (b : Fin n) (t : ℝ) :
    separationProbability (threeRowAddCell P a b t) 3 = separationProbability P 3 +
      (3 * (totalMass P ^ 2 - ∑ j, colSum P j ^ 2) + 6 * threeRowReducedGradient P a b) * t := by
  simp_rw [separationProbability_threeRow_cubic, threeRowSuccessPolynomial_grouped]
  rw [totalMass_threeRowAddCell, sum_colSum_threeRowAddCell P a b t (fun x => x ^ 2),
    sum_colSum_threeRowAddCell P a b t (fun x => x ^ 3),
    sum_rowPair_threeRowAddCell, sum_triple_threeRowAddCell]
  unfold threeRowReducedGradient
  ring

end DittertRybin
