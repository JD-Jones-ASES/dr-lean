import DR.Endpoint.RectangularPadding
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

private def oneRowInjection : Fin 1 ↪ Fin 3 :=
  ⟨fun _ => 1, fun a b _ => Subsingleton.elim a b⟩

-- Two unused columns give exactly2!, not one, completions.
example : Fintype.card (Fin 2 ↪ ↥(Set.range oneRowInjection)ᶜ) = 2 := by
  simpa using rectangular_dummy_completion_count oneRowInjection

-- With no dummy rows, the unique empty completion has cardinal0!=1.
example (e : Fin 3 ↪ Fin 3) :
    Fintype.card (Fin 0 ↪ ↥(Set.range e)ᶜ) = 1 := by
  exact rectangular_dummy_completion_count e

example : (rectangularPermutationCompletionEquiv (by decide : 1 ≤ 3)
    (Equiv.swap 0 2)).1 0 = 2 := by
  rw [rectangularPermutationCompletionEquiv_original]
  decide

private noncomputable def signedInput : Board 1 3 := fun _ _ => -2

private theorem signed_padding_value :
    (rectangularPadding (by decide : 1 ≤ 3) signedInput).permanent = -4/3 := by
  rw [permanent_rectangularPadding, rookSum_endpoint_eq_rowAvoidance]
  norm_num [rowAvoidance, rowAssignmentMass, signedInput, Nat.descFactorial]

example : (rectangularPadding (by decide : 1 ≤ 3) signedInput).permanent = -4/3 :=
  signed_padding_value

-- Omitting the dummy factorial would give the incorrect value−2/3.
example : (rectangularPadding (by decide : 1 ≤ 3) signedInput).permanent ≠ -2/3 := by
  rw [signed_padding_value]
  norm_num

example (B : Board 2 2) : (rectangularPadding (le_refl 2) B).permanent = 4*B.permanent := by
  rw [permanent_rectangularPadding, rookSum_endpoint_eq_rowAvoidance,
    rowAvoidance_square_eq_permanent]
  norm_num

example (B : Board 2 3) :
    (rectangularPadding (by decide) B).permanent = (4/3)*rookSum B 2 := by
  rw [permanent_rectangularPadding]
  norm_num

-- The all-dummy case and the empty square are retained.
example : rectangularPadding (by decide : 0 ≤ 3) (uniformBoard 0 3) =
    uniformDittertMatrix 3 := rectangularPadding_uniform _

example (B : Board 0 0) : (rectangularPadding (le_refl 0) B).permanent = 1 := by
  rw [permanent_rectangularPadding, rookSum_endpoint_eq_rowAvoidance]
  simp [rowAvoidance, rowAssignmentMass]

private noncomputable def boundaryInput : Board 2 3 := fun i j =>
  if j.val=1 then 1/6 else if (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=0) then 1/3 else 0

private theorem boundary_padding_stochastic :
    rectangularPadding (by decide : 2 ≤ 3) boundaryInput ∈ doublyStochastic ℝ (Fin 3) := by
  apply rectangularPadding_mem_doublyStochastic (by decide) (by decide) (by decide)
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [boundaryInput]
  · intro i
    fin_cases i <;> norm_num [rowSum,boundaryInput,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [colSum,boundaryInput,Fin.sum_univ_succ]

example : rectangularPadding (by decide : 2 ≤ 3) boundaryInput ∈ doublyStochastic ℝ (Fin 3) :=
  boundary_padding_stochastic

example : ∃ i j, rectangularPadding (by decide : 2 ≤ 3) boundaryInput i j = 0 := by
  apply rectangularPadding_hasZero
  exact ⟨0,0,by norm_num [boundaryInput]⟩

#print axioms sum_embedding_with_constant_rows
#print axioms rectangular_dummy_completion_count
#print axioms rectangular_dummy_completion_bijective
#print axioms rectangularPermutationCompletionEquiv
#print axioms rectangularPermutationCompletionEquiv_original
#print axioms permanent_rectangularPadding
#print axioms rectangularPadding_square
#print axioms rectangularPadding_nonneg
#print axioms rectangularPadding_mem_doublyStochastic
#print axioms rectangularPadding_uniform
#print axioms rectangularPadding_hasZero
end DittertRybin.Tests
