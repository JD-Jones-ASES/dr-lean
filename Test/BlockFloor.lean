import DR.Square.BlockFloor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Boundary and relabeling controls for the substochastic and two-block floors.
The noncontiguous four-by-four example has different row and column subsets.
-/

namespace DittertRybin.Tests.BlockFloor

open scoped BigOperators
open Matrix

-- Empty matrices retain permanent one, and the missing-mass parameter is zero.
example : dittertConstant 0 * (1 - (0 : ℝ)) ^ 0 ≤ (0 : Board 0 0).permanent := by
  exact permanent_lower_bound_of_substochastic 0 (by simp) (by simp [rowSum])
    (by simp [colSum]) 0 (by norm_num) (by norm_num)
    (by simp [totalMass, rowSum])

private noncomputable def oneBlock : Board 1 1 := fun _ _ => 2 / 3

-- In dimension one the power floor is attained exactly.
example : dittertConstant 1 * (1 - (1 / 3 : ℝ)) ^ 1 = oneBlock.permanent := by
  norm_num [dittertConstant, Matrix.permanent_unique, oneBlock]

example : dittertConstant 1 * (1 - (1 / 3 : ℝ)) ^ 1 ≤ oneBlock.permanent := by
  apply permanent_lower_bound_of_substochastic oneBlock
  · intro i j; norm_num [oneBlock]
  · intro i; norm_num [rowSum, oneBlock, Fin.sum_univ_one]
  · intro j; norm_num [colSum, oneBlock, Fin.sum_univ_one]
  · norm_num
  · norm_num
  · norm_num [totalMass, rowSum, oneBlock, Fin.sum_univ_one]

private noncomputable def sparse : Board 2 2 := !![1, 0; 0, 1 / 2]

-- A valid block may have zero entries and unequal deficits in its marginals.
example : dittertConstant 2 * (1 - (1 / 2 : ℝ)) ^ 2 ≤ sparse.permanent := by
  apply permanent_lower_bound_of_substochastic sparse
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [sparse]
  · intro i; fin_cases i <;> norm_num [rowSum, sparse, Fin.sum_univ_two]
  · intro j; fin_cases j <;> norm_num [colSum, sparse, Fin.sum_univ_two]
  · norm_num
  · norm_num
  · norm_num [totalMass, rowSum, sparse, Fin.sum_univ_two]

private noncomputable def bad : Board 2 2 := !![3 / 2, 1 / 4; 1 / 4, 0]

-- Total mass and nonnegativity alone do not imply the floor: row/column caps matter.
example : totalMass bad = 2 ∧ ¬ (∀ i, rowSum bad i ≤ 1) := by
  norm_num [totalMass, rowSum, bad, Fin.sum_univ_two, Fin.forall_fin_two]

example : ¬ dittertConstant 2 ≤ bad.permanent := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide +kernel
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide +kernel
  rw [Matrix.permanent, hu, Finset.sum_pair hne]
  norm_num [dittertConstant, bad, Fin.prod_univ_two, Equiv.swap_apply_def]

private def four : Board 4 4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
private def I4 : Finset (Fin 4) := {0, 2}
private def J4 : Finset (Fin 4) := {1, 3}

private theorem four_ds : four ∈ doublyStochastic ℝ (Fin 4) := by
  rw [mem_doublyStochastic_iff_sum]
  norm_num [four, Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem I4_compl : I4ᶜ = J4 := by decide +kernel
private theorem J4_compl : J4ᶜ = I4 := by decide +kernel

example : cutMass four I4 J4ᶜ + cutMass four I4ᶜ J4 = 0 := by
  rw [I4_compl, J4_compl]
  simp only [cutMass, I4, J4, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2), Finset.sum_pair (by decide : (1 : Fin 4) ≠ 3)]; norm_num [four, Matrix.cons_val_two, Matrix.cons_val_three]

-- Actual independent row/column partitions are used, not a contiguous principal block.
example : (1 / 4 : ℝ) ≤ four.permanent := by
  have h := permanent_lower_bound_of_two_blocks four four
    (fun i j => nonneg_of_mem_doublyStochastic four_ds) four_ds 1 (by norm_num)
    (by intro i j; simp) I4 J4 (by decide +kernel) 0
    (by rw [I4_compl, J4_compl]; simp only [cutMass, I4, J4, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2), Finset.sum_pair (by decide : (1 : Fin 4) ≠ 3)]; norm_num [four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num)
  rw [show I4.card = 2 by decide +kernel] at h
  norm_num [dittertConstant] at h ⊢
  exact h

-- Non-unit domination propagates the full nth power through the actual permanent.
example : (81 / 1024 : ℝ) ≤ ((3 / 4 : ℝ) • four).permanent := by
  have h := permanent_lower_bound_of_two_blocks ((3 / 4 : ℝ) • four) four
    (fun i j => mul_nonneg (by norm_num) (nonneg_of_mem_doublyStochastic four_ds))
    four_ds (3 / 4) (by norm_num) (by intro i j; rfl) I4 J4 (by decide +kernel) 0
    (by rw [I4_compl, J4_compl]; simp only [cutMass, I4, J4, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2), Finset.sum_pair (by decide : (1 : Fin 4) ≠ 3)]; norm_num [four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num)
  rw [show I4.card = 2 by decide +kernel] at h
  norm_num [dittertConstant] at h ⊢
  exact h

private noncomputable def near : Board 2 2 := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]

private theorem near_ds : near ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  norm_num [near, Fin.forall_fin_two, Fin.sum_univ_two]

-- Positive crossing mass uses both opposite rectangles, producing the exact w/2 term.
example : (9 / 16 : ℝ) ≤ near.permanent := by
  have hcomp : ({0} : Finset (Fin 2))ᶜ = {1} := by decide +kernel
  have h := permanent_lower_bound_of_two_blocks near near
    (fun i j => nonneg_of_mem_doublyStochastic near_ds) near_ds 1 (by norm_num)
    (by intro i j; simp) {0} {0} rfl (1 / 2)
    (by rw [hcomp]; norm_num [cutMass, near]) (by norm_num)
  norm_num [dittertConstant] at h
  exact h

-- Halving the crossing penalty again would assert a false permanent lower bound.
example : ¬ (1 - (1 / 2 : ℝ) / 4) ^ 2 ≤ near.permanent := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide +kernel
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide +kernel
  rw [Matrix.permanent, hu, Finset.sum_pair hne]
  norm_num [near, Fin.prod_univ_two, Equiv.swap_apply_def]

#print axioms DittertRybin.permanent_lower_bound_of_substochastic
#print axioms DittertRybin.permanent_squareCutBlocks_le
#print axioms DittertRybin.permanent_lower_bound_of_two_blocks

end DittertRybin.Tests.BlockFloor
