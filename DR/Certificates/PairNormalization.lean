import DR.Certificates.Gram
import Mathlib.Logic.Equiv.Basic

/-! Actual permutations send a pair of labels to its equality-pattern representative.
No unused labels or ambient-dimension census is needed. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def pairNormalization {α : Type*} [DecidableEq α] (z o a b : α) : Equiv.Perm α :=
  if a=b then Equiv.swap z a else
    (Equiv.swap z a).trans (Equiv.swap o (Equiv.swap z a b))

theorem pairNormalization_first {α : Type*} [DecidableEq α]
    (z o a b : α) (hzo : z≠o) : pairNormalization z o a b a=z := by
  by_cases hab : a=b
  · simp only [pairNormalization,if_pos hab,Equiv.swap_apply_right]
  · have hb : z≠Equiv.swap z a b := by
      intro he
      have h := (Equiv.swap z a).injective ((Equiv.swap_apply_right z a).trans he)
      exact hab h
    simp only [pairNormalization,if_neg hab,Equiv.trans_apply,Equiv.swap_apply_right]
    exact Equiv.swap_apply_of_ne_of_ne hzo hb

theorem pairNormalization_second {α : Type*} [DecidableEq α]
    (z o a b : α) : pairNormalization z o a b b=(if a=b then z else o) := by
  by_cases hab : a=b
  · subst b
    simp only [pairNormalization,if_true,Equiv.swap_apply_right]
  · simp only [pairNormalization,if_neg hab,Equiv.trans_apply,Equiv.swap_apply_right]

/-- Reindexing is an equality of the actual quadratic sums on all real vectors. -/
theorem quadraticValue_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (σ : κ ≃ ι) (x : κ → ℝ) :
    quadraticValue (Q.submatrix σ σ) x=quadraticValue Q (fun i => x (σ.symm i)) := by
  unfold quadraticValue
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply,Matrix.submatrix_apply]

end DittertRybin.Certificates
