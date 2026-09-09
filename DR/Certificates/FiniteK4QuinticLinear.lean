import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! The sparse local coefficient identity is a sum over fibers of ten
choices. Padding slots are allowed: their fiber must have exact zero weight.
Every slot equation is an integer identity checked separately in the data gates. -/
namespace DittertRybin.Certificates
open scoped BigOperators

/-- An arbitrary finite weighted sum can be grouped by the actual chosen slot. -/
theorem sum_slot_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (slot : α → β) (w : α → ℝ) (f : β → ℝ) :
    (∑ q, w q * f (slot q)) = ∑ k, (∑ q, if slot q = k then w q else 0) * f k := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Exact integer fiber equations imply the real sparse linear identity.
No independence, uniqueness of term keys, or omitted-support assumption is used. -/
theorem quintic_sparse_fiber_identity (terms : Fin 10 → Fin 407 × Nat)
    (roles : Fin 10 → Fin 407) (weights : Fin 10 → Nat) (slots : Fin 10 → Fin 10)
    (multiplicity : Nat) (coeff : Fin 407 → ℝ)
    (hrole : ∀ q, roles q = (terms (slots q)).1)
    (hfiber : ∀ k, multiplicity * (∑ q, if slots q = k then weights q else 0) =
      60 * (terms k).2) :
    (multiplicity : ℝ) * (∑ q, (weights q : ℝ) * coeff (roles q)) =
      60 * ∑ k, ((terms k).2 : ℝ) * coeff (terms k).1 := by
  simp_rw [hrole]
  rw [sum_slot_fibers slots (fun q => (weights q : ℝ)) (fun k => coeff (terms k).1)]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [← mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun a : Nat => (a : ℝ)) (hfiber k)
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_ofNat] at h
  rw [h]

end DittertRybin.Certificates
