import DR.Probability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Signed iid reindexing for quartic certificates

Coordinate permutations preserve independent sample weights. Removing one
coordinate contributes the total one-sample mass, without dividing by that
mass. These identities therefore include signed and zero-total-mass inputs,
as well as empty outcome types.
-/

namespace DittertRybin
open scoped BigOperators

/-- Relabel the positions of an ordered sample. -/
def samplePermutationEquiv {α : Type*} {k : ℕ} (e : Equiv.Perm (Fin k)) :
    (Fin k → α) ≃ (Fin k → α) where
  toFun s := s ∘ e
  invFun s := s ∘ e.symm
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

theorem sampleMass_permutation {α : Type*} {k : ℕ} (p : α → ℝ)
    (e : Equiv.Perm (Fin k)) (s : Fin k → α) :
    sampleMass p (s ∘ e) = sampleMass p s := by
  exact Equiv.prod_comp e (fun i => p (s i))

/-- Arbitrary observables may be permuted under signed iid summation. -/
theorem sum_sampleMass_permutation {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (e : Equiv.Perm (Fin k)) (f : (Fin k → α) → ℝ) :
    (∑ s : Fin k → α, sampleMass p s * f (s ∘ e)) =
      ∑ s : Fin k → α, sampleMass p s * f s := by
  classical
  apply Fintype.sum_equiv (samplePermutationEquiv e)
  intro s
  change sampleMass p s * f (s ∘ e) = sampleMass p (s ∘ e) * f (s ∘ e)
  rw [sampleMass_permutation]

/-- Deleting any one position multiplies the retained-sample sum by the total mass. -/
theorem sum_sampleMass_delete {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (a : Fin (k + 1)) (f : (Fin k → α) → ℝ) :
    (∑ s : Fin (k + 1) → α, sampleMass p s * f (s ∘ a.succAbove)) =
      (∑ x, p x) * ∑ s : Fin k → α, sampleMass p s * f s := by
  classical
  calc
    _ = ∑ q : α × (Fin k → α), p q.1 * sampleMass p q.2 * f q.2 := by
      apply Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (k + 1) => α) a).symm
      intro s
      change sampleMass p s * f (s ∘ a.succAbove) =
        p (s a) * sampleMass p (s ∘ a.succAbove) * f (s ∘ a.succAbove)
      rw [sampleMass, Fin.prod_univ_succAbove _ a]
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Four ordered positions are exactly four independently chosen outcomes. -/
def sampleFourEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun s := (s 0, s 1, s 2, s 3)
  invFun s := ![s.1, s.2.1, s.2.2.1, s.2.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv s := rfl

theorem sum_sample_four {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  classical
  rw [← (sampleFourEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

end DittertRybin
